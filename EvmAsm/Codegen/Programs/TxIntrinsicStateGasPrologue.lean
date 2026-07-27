/-
  Prologue (instr 0–13) for `tx_intrinsic_state_gas`.

  allocate 64-byte frame → storeSeq ra/s0–s6 → MV ABI a0–a2 into
  s0/s1/s2 and restore a0/a1 from s0/s1. Leaves PC at T+56 (la extract).
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

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

theorem regsAt_tisFrame (s : TisSaved) :
    regsAt tisFrame (tisSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6)) := by
  simp [tisFrame, regsAt, tisSavedVals, sepConj_emp_right']

theorem frameSlotsSaved_tisFrame (spC : Word) (s : TisSaved) :
    frameSlotsSaved tisFrame spC (tisSavedVals s) =
      ((spC + signExtend12 (0 : BitVec 12) ↦ₘ s.ra) **
        (spC + signExtend12 (8 : BitVec 12) ↦ₘ s.s0) **
        (spC + signExtend12 (16 : BitVec 12) ↦ₘ s.s1) **
        (spC + signExtend12 (24 : BitVec 12) ↦ₘ s.s2) **
        (spC + signExtend12 (32 : BitVec 12) ↦ₘ s.s3) **
        (spC + signExtend12 (40 : BitVec 12) ↦ₘ s.s4) **
        (spC + signExtend12 (48 : BitVec 12) ↦ₘ s.s5) **
        (spC + signExtend12 (56 : BitVec 12) ↦ₘ s.s6)) := by
  simp [tisFrame, frameSlotsSaved, tisSavedVals, sepConj_emp_right']

/-- ABI args + temps carried through the prologue. -/
def prologueAbiRest
    (txBase txLenW outPtr : Word)
    (old5 old6 old7 old13 old14 old15 old16 : Word) : Assertion :=
  (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
  (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
  (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Post-prologue (PC = T+56): frame saved, ABI in s0/s1/s2, a0/a1 restored. -/
def prologuePost (spC : Word) (s : TisSaved)
    (txBase txLenW outPtr : Word)
    (old5 old6 old7 old13 old14 old15 old16 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ s.ra) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) ** (.x18 ↦ᵣ outPtr) **
  (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
  frameSlotsSaved tisFrame spC (tisSavedVals s) **
  prologueAbiRest txBase txLenW outPtr old5 old6 old7 old13 old14 old15 old16

set_option maxRecDepth 8000 in
/-- Five ABI moves (instr 9-13): s0=a0, s1=a1, s2=a2, a0=s0, a1=s1. -/
theorem tisAbiMoves
    (txBase txLenW outPtr : Word)
    (cs0 cs1 cs2 : Word) :
    cpsTripleWithin 5 (T + 36) (T + 56) tisCode
      ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) ** (.x18 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr)) := by
  have h0 := mv_spec_gen_within .x8 .x10 txBase cs0 (T + 36) (by decide)
  have h1 := mv_spec_gen_within .x9 .x11 txLenW cs1 (T + 40) (by decide)
  have h2 := mv_spec_gen_within .x18 .x12 outPtr cs2 (T + 44) (by decide)
  have h3 := mv_spec_gen_within .x10 .x8 txBase txBase (T + 48) (by decide)
  have h4 := mv_spec_gen_within .x11 .x9 txLenW txLenW (T + 52) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T (T + 36) tisProg 9
      (.MV .x8 .x10) (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) h0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T (T + 40) tisProg 10
      (.MV .x9 .x11) (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) h1
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T (T + 44) tisProg 11
      (.MV .x18 .x12) (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) h2
  have e3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T (T + 48) tisProg 12
      (.MV .x10 .x8) (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) h3
  have e4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T (T + 52) tisProg 13
      (.MV .x11 .x9) (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) h4
  runBlock e0 e1 e2 e3 e4

set_option maxRecDepth 8000 in
/-- Frame allocate + storeSeq (instr 0-8): 1 ADDI + 8 SD. -/
theorem tisFrameSave (sp0 spC : Word) (s : TisSaved)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 9 T (T + 36) tisCode
      ((.x2 ↦ᵣ sp0) ** regsAt tisFrame (tisSavedVals s) **
        frameSlotsOwn tisFrame spC)
      ((.x2 ↦ᵣ spC) ** regsAt tisFrame (tisSavedVals s) **
        frameSlotsSaved tisFrame spC (tisSavedVals s)) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-64 : BitVec 12) T (by decide)
  rw [← hspC] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T T tisProg 0
      (.ADDI .x2 .x2 (-64 : BitVec 12)) rfl
      (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt tisFrame (tisSavedVals s) ** frameSlotsOwn tisFrame spC) (by pcf) ha
  have hs0 := storeSeq_spec tisFrame spC (tisSavedVals s) (T + 4) (by decide)
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (T + 4) (storeProg tisFrame) a = some i →
        tisCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub T (T + 4) tisProg (storeProg tisFrame) 1
      (by bv_omega) rfl
      (by rw [tis_length]; simp [tisFrame, storeProg])
      (by rw [tis_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show T + 4 + BitVec.ofNat 64 (4 * tisFrame.length) = T + 36 from by
    simp [tisFrame]; bv_omega] at hs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hs

set_option maxRecDepth 8000 in
/-- Full prologue: frame save + ABI moves (instr 0-13 to T+56). -/
theorem tisPrologue (sp0 spC : Word) (s : TisSaved)
    (txBase txLenW outPtr : Word)
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 14 T (T + 56) tisCode
      ((.x2 ↦ᵣ sp0) ** regsAt tisFrame (tisSavedVals s) **
        frameSlotsOwn tisFrame spC **
        prologueAbiRest txBase txLenW outPtr old5 old6 old7 old13 old14 old15 old16)
      (prologuePost spC s txBase txLenW outPtr
        old5 old6 old7 old13 old14 old15 old16) := by
  have hsave := tisFrameSave sp0 spC s hspC
  have hsaveF := cpsTripleWithin_frameR
    (prologueAbiRest txBase txLenW outPtr old5 old6 old7 old13 old14 old15 old16)
    (by pcf) hsave
  have hmv := tisAbiMoves txBase txLenW outPtr s.s0 s.s1 s.s2
  have hmvF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      frameSlotsSaved tisFrame spC (tisSavedVals s) **
      (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hmv
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_tisFrame] at hp
    unfold prologueAbiRest at hp
    xperm_hyp hp) hsaveF hmvF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold prologuePost prologueAbiRest
      xperm_hyp hq) h01

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
