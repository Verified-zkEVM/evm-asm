/-
  Prologue (instr 0–20) for `block_verdict_tx_state_gas_array`.

  allocate 112-byte frame → storeSeq ra/s0–s11 → MV ABI a0–a6 into
  s0/s1/s2/s3/s8/s9/s10. Leaves PC at B+84 (header-validation entry).
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

/-- Frame descriptor matching the 13 `SD` slots in the Program. -/
def bvtFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16),
   (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48),
   (.x22, 56), (.x23, 64), (.x24, 72), (.x25, 80),
   (.x26, 88), (.x27, 96)]

theorem bvtFrame_length : bvtFrame.length = 13 := by decide

def savedVals (s : Saved) : Reg → Word
  | .x1  => s.ra
  | .x8  => s.s0
  | .x9  => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | .x23 => s.s7
  | .x24 => s.s8
  | .x25 => s.s9
  | .x26 => s.s10
  | .x27 => s.s11
  | _ => 0

theorem regsAt_bvtFrame (s : Saved) :
    regsAt bvtFrame (savedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11)) := by
  simp [bvtFrame, regsAt, savedVals, sepConj_emp_right']

theorem frameSlotsSaved_bvtFrame (spC : Word) (s : Saved) :
    frameSlotsSaved bvtFrame spC (savedVals s) = savedFrame spC s := by
  simp [bvtFrame, frameSlotsSaved, savedFrame, savedVals, sepConj_emp_right']

/-- ABI argument rest carried through the prologue. -/
def prologueAbiRest
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (old5 old6 old7 : Word) : Assertion :=
  (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ countW) **
  (.x13 ↦ᵣ outBase) ** (.x14 ↦ᵣ balBase) ** (.x15 ↦ᵣ balLenW) **
  (.x16 ↦ᵣ chainIdW) **
  (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Post-prologue (PC = B+84): frame saved, ABI copied into s-regs. -/
def prologuePost (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (old5 old6 old7 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ s.ra) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
  (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
  (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
  (.x27 ↦ᵣ s.s11) **
  savedFrame spC s **
  prologueAbiRest txBase txLenW countW outBase balBase balLenW chainIdW
    old5 old6 old7

set_option maxRecDepth 8000 in
/-- Seven ABI moves (instr 14-20). -/
theorem bvtAbiMoves
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (cs0 cs1 cs2 cs3 cs8 cs9 cs10 : Word) :
    cpsTripleWithin 7 (B + 56) (B + 84) bvtCode
      ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
        (.x24 ↦ᵣ cs8) ** (.x25 ↦ᵣ cs9) ** (.x26 ↦ᵣ cs10) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ countW) **
        (.x13 ↦ᵣ outBase) ** (.x14 ↦ᵣ balBase) ** (.x15 ↦ᵣ balLenW) **
        (.x16 ↦ᵣ chainIdW))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) ** (.x18 ↦ᵣ countW) **
        (.x19 ↦ᵣ outBase) ** (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) **
        (.x26 ↦ᵣ chainIdW) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ countW) **
        (.x13 ↦ᵣ outBase) ** (.x14 ↦ᵣ balBase) ** (.x15 ↦ᵣ balLenW) **
        (.x16 ↦ᵣ chainIdW)) := by
  have h0 := mv_spec_gen_within .x8 .x10 txBase cs0 (B + 56) (by decide)
  have h1 := mv_spec_gen_within .x9 .x11 txLenW cs1 (B + 60) (by decide)
  have h2 := mv_spec_gen_within .x18 .x12 countW cs2 (B + 64) (by decide)
  have h3 := mv_spec_gen_within .x19 .x13 outBase cs3 (B + 68) (by decide)
  have h4 := mv_spec_gen_within .x24 .x14 balBase cs8 (B + 72) (by decide)
  have h5 := mv_spec_gen_within .x25 .x15 balLenW cs9 (B + 76) (by decide)
  have h6 := mv_spec_gen_within .x26 .x16 chainIdW cs10 (B + 80) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 56) bvtProg 14
      (.MV .x8 .x10) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 60) bvtProg 15
      (.MV .x9 .x11) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h1
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 64) bvtProg 16
      (.MV .x18 .x12) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h2
  have e3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 68) bvtProg 17
      (.MV .x19 .x13) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h3
  have e4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 72) bvtProg 18
      (.MV .x24 .x14) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h4
  have e5 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 76) bvtProg 19
      (.MV .x25 .x15) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h5
  have e6 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 80) bvtProg 20
      (.MV .x26 .x16) (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) h6
  runBlock e0 e1 e2 e3 e4 e5 e6

set_option maxRecDepth 8000 in
/-- Frame allocate + storeSeq (instr 0-13). -/
theorem bvtFrameSave (sp0 spC : Word) (s : Saved)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12)) :
    cpsTripleWithin 14 B (B + 56) bvtCode
      ((.x2 ↦ᵣ sp0) ** regsAt bvtFrame (savedVals s) **
        frameSlotsOwn bvtFrame spC)
      ((.x2 ↦ᵣ spC) ** regsAt bvtFrame (savedVals s) **
        frameSlotsSaved bvtFrame spC (savedVals s)) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-112 : BitVec 12) B (by decide)
  rw [← hspC] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B B bvtProg 0
      (.ADDI .x2 .x2 (-112 : BitVec 12)) rfl
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt bvtFrame (savedVals s) ** frameSlotsOwn bvtFrame spC) (by pcf) ha
  have hs0 := storeSeq_spec bvtFrame spC (savedVals s) (B + 4) (by decide)
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg bvtFrame) a = some i →
        bvtCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub B (B + 4) bvtProg (storeProg bvtFrame) 1
      (by bv_omega) rfl
      (by rw [bvt_length]; simp [bvtFrame, storeProg])
      (by rw [bvt_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show B + 4 + BitVec.ofNat 64 (4 * bvtFrame.length) = B + 56 from by
    simp [bvtFrame]; bv_omega] at hs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hs

set_option maxRecDepth 8000 in
/-- Full prologue: frame save + ABI moves (instr 0-20 to B+84). -/
theorem bvtPrologue (sp0 spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (old5 old6 old7 : Word)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12)) :
    cpsTripleWithin 21 B (B + 84) bvtCode
      ((.x2 ↦ᵣ sp0) ** regsAt bvtFrame (savedVals s) **
        frameSlotsOwn bvtFrame spC **
        prologueAbiRest txBase txLenW countW outBase balBase balLenW chainIdW
          old5 old6 old7)
      (prologuePost spC s txBase txLenW countW outBase balBase balLenW chainIdW
        old5 old6 old7) := by
  have hsave := bvtFrameSave sp0 spC s hspC
  have hsaveF := cpsTripleWithin_frameR
    (prologueAbiRest txBase txLenW countW outBase balBase balLenW chainIdW
      old5 old6 old7) (by pcf) hsave
  have hmv := bvtAbiMoves txBase txLenW countW outBase balBase balLenW chainIdW
    s.s0 s.s1 s.s2 s.s3 s.s8 s.s9 s.s10
  have hmvF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) ** (.x27 ↦ᵣ s.s11) **
      savedFrame spC s **
      (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hmv
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_bvtFrame, frameSlotsSaved_bvtFrame] at hp
    unfold prologueAbiRest at hp
    xperm_hyp hp) hsaveF hmvF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold prologuePost prologueAbiRest
      xperm_hyp hq) h01

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
