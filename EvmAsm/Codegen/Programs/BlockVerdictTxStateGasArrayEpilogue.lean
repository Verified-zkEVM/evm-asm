/-
  Status-ok + frame restore epilogue for `block_verdict_tx_state_gas_array`.

  StatusOk (B+296): LI a0,0; JAL +24 to restore at B+324:
  loadSeq ra/s0-s11; ADDI sp,+112; JALR ret.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoop
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayPrologue
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray pcFree_wordArray)

local macro "bvt_pcf" : tactic => `(tactic|
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | exact pcFree_wordArray _ _
    | exact pcFree_emp
    | exact pcFree_pure
    | exact pcFree_regsAt _ _
    | exact pcFree_frameSlotsSaved _ _ _
    | unfold payload; skip
    | unfold savedFrame; skip
    | unfold scratchRegs; skip
    | unfold scratchRegsNoA0; skip)

abbrev EpiRestore : Word := B + 324
abbrev EpiAddi : Word := B + 376
abbrev EpiJalr : Word := B + 380

theorem bvtFrame_hne : ∀ p ∈ bvtFrame, p.1 ≠ .x0 := by decide

set_option maxRecDepth 8000 in
/-- loadSeq + ADDI sp + JALR (instr 81-95). Exit at s.ra when ra is even. -/
theorem bvtEpilogueRestore (sp0 spC : Word) (s cur : Saved)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 15 EpiRestore s.ra bvtCode
      ((.x2 ↦ᵣ spC) ** regsAt bvtFrame (savedVals cur) **
        frameSlotsSaved bvtFrame spC (savedVals s))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
        (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved bvtFrame spC (savedVals s)) := by
  have hs0 := loadSeq_spec bvtFrame spC (savedVals s) (savedVals cur) (B + 324)
    (by decide) bvtFrame_hne
  have h_loadMono : ∀ a i,
      CodeReq.ofProg (B + 324) (loadProg bvtFrame) a = some i →
        bvtCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub B (B + 324) bvtProg (loadProg bvtFrame) 81
      (by bv_omega) (by rfl)
      (by rw [bvt_length]; simp [bvtFrame, loadProg])
      (by rw [bvt_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  rw [show B + 324 + BitVec.ofNat 64 (4 * bvtFrame.length) = B + 376 from by
    simp [bvtFrame]; bv_omega] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (112 : BitVec 12) (B + 376) (by decide)
  have hsp : spC + signExtend12 (112 : BitVec 12) = sp0 := by
    rw [hspC]
    rw [show signExtend12 (-112 : BitVec 12) = (-112 : Word) from by decide,
      show signExtend12 (112 : BitVec 12) = (112 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 376) bvtProg 94
      (.ADDI .x2 .x2 (112 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt bvtFrame (savedVals s) ** frameSlotsSaved bvtFrame spC (savedVals s))
    (by bvt_pcf) ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hs haF
  have hpc : (B + 376 : Word) + 4 = B + 380 := by bv_omega
  rw [hpc] at hload_addi
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' (B + 380) s.ra
  rw [hret] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 380) bvtProg 95
      (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
      (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
      (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
      frameSlotsSaved bvtFrame spC (savedVals s))
    (by bvt_pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_bvtFrame] at hp
    xperm_hyp hp) hload_addi hjalrF
  have hn : bvtFrame.length + 1 + 1 = 15 := by simp [bvtFrame]
  rw [hn] at hall
  -- Align EpiRestore abbrev with B+324
  change cpsTripleWithin 15 EpiRestore s.ra bvtCode _ _
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- StatusOk: LI a0,0; JAL +24; restore. Lands at caller ra with a0=0. -/
theorem bvtStatusOk (sp0 spC : Word) (s cur : Saved) (o10 : Word)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 17 StatusOk s.ra bvtCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) **
        regsAt bvtFrame (savedVals cur) **
        frameSlotsSaved bvtFrame spC (savedVals s))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
        (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved bvtFrame spC (savedVals s)) := by
  -- LI + JAL as a 2-instr block (retViolation pattern; avoids framing empAssertion)
  have hli0 := li_spec_gen_within .x10 o10 (0 : Word) StatusOk (by decide)
  have hli := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B StatusOk bvtProg 74
      (.LI .x10 (0 : Word))
      (by simp only [StatusOk]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hli0
  have hjal0 := jal_x0_spec_gen_within (24 : BitVec 21) (StatusOk + 4)
  have hjal := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (StatusOk + 4) bvtProg 75
      (.JAL .x0 (24 : BitVec 21))
      (by simp only [StatusOk]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hjal0
  have hjalPc : StatusOk + 4 + signExtend21 (24 : BitVec 21) = B + 324 := by
    simp only [StatusOk]
    rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by decide]
    bv_omega
  rw [hjalPc] at hjal
  have hblock : cpsTripleWithin 2 StatusOk (B + 324) bvtCode
      (.x10 ↦ᵣ o10)
      (.x10 ↦ᵣ (0 : Word)) := by
    runBlock hli hjal
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** regsAt bvtFrame (savedVals cur) **
      frameSlotsSaved bvtFrame spC (savedVals s))
    (by bvt_pcf) hblock
  have hrest := bvtEpilogueRestore sp0 spC s cur hspC hret
  have hrestF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)))
    (by exact pcFree_regIs) hrest
  change cpsTripleWithin 15 (B + 324) s.ra bvtCode _ _ at hrestF
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hblockF hrestF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Guard-taken → status-ok exit under full prefix

    When `i = n` and `successCells` holds, exit with `postOk`.
    Peels `regOwn` temps from `LoopInv` into concrete `regsAt` for restore.
-/

/-- Current s-reg snapshot at loop exit (`i = n`): ABI bases + count. -/
def exitCur (txBase outBase balBase chainIdW nW : Word)
    (txBlob balBytes : List (BitVec 8)) (n : Nat)
    (o1 o22 o23 o27 : Word) : Saved where
  ra  := o1
  s0  := txBase
  s1  := BitVec.ofNat 64 txBlob.length
  s2  := nW
  s3  := outBase
  s4  := nW
  s5  := BitVec.ofNat 64 n
  s6  := o22
  s7  := o23
  s8  := balBase
  s9  := BitVec.ofNat 64 balBytes.length
  s10 := chainIdW
  s11 := o27

set_option maxRecDepth 8000 in
/-- LoopInv at `i = n` + successCells → postOk via guard-taken + status-ok. -/
theorem bvtExitOk (sp0 spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (txBlob : List (BitVec 8))
    (outVals : List Nat) (balBytes : List (BitVec 8))
    (chainId : Nat) (balEnabled : Bool) (n : Nat)
    (hnW : nW = BitVec.ofNat 64 n)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : csaved.ra &&& ~~~(1 : Word) = csaved.ra)
    (hsucc : successCells teer txs balBytes chainId balEnabled outVals) :
    cpsTripleWithin 18 LoopGuard csaved.ra bvtCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled n)
      (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
        chainId balEnabled outVals) := by
  -- 1. Guard taken preserves LoopInv → StatusOk
  have hguard := bvtGuardTaken spC txBase outBase balBase chainIdW nW csaved
    txBlob outVals balBytes balEnabled n hnW
  -- 2. At StatusOk, peel owns and run status-ok framed with payload/scratch/pure
  have hstat : cpsTripleWithin 17 StatusOk csaved.ra bvtCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled n)
      (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
        chainId balEnabled outVals) := by
    unfold LoopInv scratchRegs
    -- Peel x1, x22, x23, x27, x10 (rightmost each time)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin 17 StatusOk csaved.ra bvtCode
        (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 n) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) **
            savedFrame spC csaved **
            payload txBase outBase balBase txBlob outVals balBytes balEnabled **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x22 ** regOwn .x23 ** regOwn .x27 ** regOwn .x10) **
          regOwn .x1)
        (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
          chainId balEnabled outVals) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x1) (fun o1 => ?_)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin 17 StatusOk csaved.ra bvtCode
        (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 n) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** (.x1 ↦ᵣ o1) **
            savedFrame spC csaved **
            payload txBase outBase balBase txBlob outVals balBytes balEnabled **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x23 ** regOwn .x27 ** regOwn .x10) **
          regOwn .x22)
        (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
          chainId balEnabled outVals) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x22) (fun o22 => ?_)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin 17 StatusOk csaved.ra bvtCode
        (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 n) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** (.x1 ↦ᵣ o1) ** (.x22 ↦ᵣ o22) **
            savedFrame spC csaved **
            payload txBase outBase balBase txBlob outVals balBytes balEnabled **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x27 ** regOwn .x10) **
          regOwn .x23)
        (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
          chainId balEnabled outVals) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x23) (fun o23 => ?_)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin 17 StatusOk csaved.ra bvtCode
        (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 n) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** (.x1 ↦ᵣ o1) ** (.x22 ↦ᵣ o22) ** (.x23 ↦ᵣ o23) **
            savedFrame spC csaved **
            payload txBase outBase balBase txBlob outVals balBytes balEnabled **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x10) **
          regOwn .x27)
        (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
          chainId balEnabled outVals) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x27) (fun o27 => ?_)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin 17 StatusOk csaved.ra bvtCode
        (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 n) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) **
            (.x1 ↦ᵣ o1) ** (.x22 ↦ᵣ o22) ** (.x23 ↦ᵣ o23) ** (.x27 ↦ᵣ o27) **
            savedFrame spC csaved **
            payload txBase outBase balBase txBlob outVals balBytes balEnabled **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word))) **
          regOwn .x10)
        (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
          chainId balEnabled outVals) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10) (fun o10 => ?_)
    set cur : Saved :=
      exitCur txBase outBase balBase chainIdW nW txBlob balBytes n o1 o22 o23 o27
    have hstat0 := bvtStatusOk sp0 spC csaved cur o10 hspC hret
    -- Frame payload + scratch only (inject pure on post, GasUsed retAllValid style)
    have hG :
        (payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word))).pcFree := by
      unfold payload
      cases balEnabled <;> bvt_pcf
    have hstatF := cpsTripleWithin_frameR
      (payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      hG hstat0
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        rw [regsAt_bvtFrame, frameSlotsSaved_bvtFrame]
        simp only [cur, exitCur]
        xperm_hyp hp)
      (fun _ hq => by
        unfold postOk commonRet scratchRegsNoA0
        rw [frameSlotsSaved_bvtFrame] at hq
        refine (sepConj_pure_left _).2 ⟨hsucc, ?_⟩
        xperm_hyp hq)
      hstatF
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hguard hstat
  exact hall

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
