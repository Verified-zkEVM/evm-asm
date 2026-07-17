/-
  Loop teer path + bal0 FromIntrinsic for `block_verdict_tx_state_gas_array` (a4gbr).
  Split for Codegen/Programs 1500-line file-size guard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoopEnd
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom)

local macro "bvt_pcf" : tactic => `(tactic|
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | exact pcFree_wordArray _ _
    | exact pcFree_wordArrayFrom _ _ _
    | exact pcFree_emp
    | exact pcFree_pure
    | unfold payload; skip
    | unfold savedFrame; skip
    | unfold scratchRegs; skip)

/-! ## Post-intrinsic bal≠0 teer + store tail (instr 55–69 + 72–73)

    a0=0 → BNE ntaken; bal≠0 → BEQ ntaken; setup teer ABI; call teer;
    LD/ADD/SD out[i] += teer; JAL to LoopAdvance; i++; back-edge.
-/

abbrev AfterBalCheck : Word := B + 228
abbrev AfterTeerSetup : Word := B + 252
abbrev AfterStore : Word := B + 276

abbrev teerJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_eip7702_existing_authority_refund
    (GuestAddrs.block_verdict_tx_state_gas_array + 252)

/-- Ambient for bal≠0 post-intrinsic path (balBase ≠ 0, bal region present).
    Excludes focus regs x0/x10/x24 for BNE/BEQ. -/

def teerRest (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word) : Assertion :=
  (.x1 ↦ᵣ LinkIntrinsic) **
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  bytesRegion txBase txBlob **
  wordArray outBase outVals **
  bytesRegion balBase balBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem teerRest_pcFree (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word) :
    (teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
      balBytes startW endW iW).pcFree := by
  unfold teerRest savedFrame; bvt_pcf

set_option maxRecDepth 8000 in
/-- Instr 55: BNE a0,x0 ntaken when a0=0 (bal≠0 ambient). -/
theorem bvtIterBneOkBal
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word) :
    cpsTripleWithin 1 LinkIntrinsic AfterIntrinsicBne bvtCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW) := by
  have hbr := bne_spec_gen_within .x10 .x0 (100 : BitVec 13)
    (0 : Word) (0 : Word) LinkIntrinsic
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B LinkIntrinsic bvtProg 55
      (.BNE .x10 .x0 (100 : BitVec 13))
      (by simp only [LinkIntrinsic]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkIntrinsic + 4 = AfterIntrinsicBne := by
    simp only [LinkIntrinsic, AfterIntrinsicBne]; bv_omega
  rw [hpc] at hnt
  have hF :
      (((.x24 ↦ᵣ balBase) **
          teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
            balBytes startW endW iW) : Assertion).pcFree := by
    unfold teerRest savedFrame; bvt_pcf
  have hntF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ balBase) **
      teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes startW endW iW) hF hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hntF

set_option maxRecDepth 8000 in
/-- Instr 56: BEQ bal,x0 ntaken when balBase ≠ 0 → AfterBalCheck. -/
theorem bvtIterBalNezFall
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW : Word)
    (hbal : balBase ≠ 0) :
    cpsTripleWithin 1 AfterIntrinsicBne AfterBalCheck bvtCode
      ((.x24 ↦ᵣ balBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW)
      ((.x24 ↦ᵣ balBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW) := by
  have hbr := beq_spec_gen_within .x24 .x0 (64 : BitVec 13)
    balBase (0 : Word) AfterIntrinsicBne
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterIntrinsicBne bvtProg 56
      (.BEQ .x24 .x0 (64 : BitVec 13))
      (by simp only [AfterIntrinsicBne]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hrest).2 hbal)
  have hpc : AfterIntrinsicBne + 4 = AfterBalCheck := by
    simp only [AfterIntrinsicBne, AfterBalCheck]; bv_omega
  rw [hpc] at hnt
  have hF :
      (((.x10 ↦ᵣ (0 : Word)) **
          teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
            balBytes startW endW iW) : Assertion).pcFree := by
    unfold teerRest savedFrame; bvt_pcf
  have hntF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) **
      teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes startW endW iW) hF hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hntF

set_option maxRecDepth 8000 in
/-- Instr 57–62: teer ABI setup → AfterTeerSetup with a0..a5 filled. -/
theorem bvtIterTeerSetup
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW : Word) (i : Nat)
    (old10 old11 old12 old13 old14 old15 : Word)
    (_hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let balLenW := BitVec.ofNat 64 balBytes.length
    let baiW := BitVec.ofNat 64 (i + 1)
    cpsTripleWithin 6 AfterBalCheck AfterTeerSetup bvtCode
      ((.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
        (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ iW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
        (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ iW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW txPtr txLenW balLenW baiW
  -- 57 ADD a0, s0, s6 (txBase + start)
  have e57_0 := add_spec_gen_within .x10 .x8 .x22 txBase startW old10
    AfterBalCheck (by decide)
  have e57C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterBalCheck bvtProg 57
      (.ADD .x10 .x8 .x22)
      (by simp only [AfterBalCheck]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e57_0
  have e57F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e57C
  have hpc57 : AfterBalCheck + 4 = B + 232 := by
    simp only [AfterBalCheck]; bv_omega
  rw [hpc57] at e57F
  -- 58 SUB a1, s7, s6 (end - start); a1 starts as old11
  have e58_0 := sub_spec_gen_within .x11 .x23 .x22 endW startW old11
    (B + 232) (by decide)
  have e58C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 232) bvtProg 58
      (.SUB .x11 .x23 .x22)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e58_0
  have e58F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x12 ↦ᵣ old12) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e58C
  have hpc58 : (B + 232) + 4 = B + 236 := by bv_omega
  rw [hpc58] at e58F
  -- 59 MV a2, s8 (bal)
  have e59_0 := mv_spec_gen_within .x12 .x24 balBase old12 (B + 236) (by decide)
  have e59C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 236) bvtProg 59
      (.MV .x12 .x24)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e59_0
  have e59F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e59C
  have hpc59 : (B + 236) + 4 = B + 240 := by bv_omega
  rw [hpc59] at e59F
  -- 60 MV a3, s9 (bal_len)
  have e60_0 := mv_spec_gen_within .x13 .x25 balLenW old13 (B + 240) (by decide)
  have e60C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 240) bvtProg 60
      (.MV .x13 .x25)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e60_0
  have e60F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
      (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x26 ↦ᵣ chainIdW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e60C
  have hpc60 : (B + 240) + 4 = B + 244 := by bv_omega
  rw [hpc60] at e60F
  -- 61 MV a4, s10 (chain_id)
  have e61_0 := mv_spec_gen_within .x14 .x26 chainIdW old14 (B + 244) (by decide)
  have e61C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 244) bvtProg 61
      (.MV .x14 .x26)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e61_0
  have e61F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
      (.x13 ↦ᵣ balLenW) ** (.x15 ↦ᵣ old15) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) **
      (.x21 ↦ᵣ iW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e61C
  have hpc61 : (B + 244) + 4 = B + 248 := by bv_omega
  rw [hpc61] at e61F
  -- 62 ADDI a5, s5, 1 (i+1); addi order is (rs1 ** rd)
  have e62_0 := addi_spec_gen_within .x15 .x21 old15 iW (1 : BitVec 12)
    (B + 248) (by decide)
  have e62_1 : cpsTripleWithin 1 (B + 248) ((B + 248) + 4)
      (CodeReq.singleton (B + 248) (.ADDI .x15 .x21 (1 : BitVec 12)))
      ((.x21 ↦ᵣ iW) ** (.x15 ↦ᵣ old15))
      ((.x21 ↦ᵣ iW) ** (.x15 ↦ᵣ baiW)) := by
    have h := e62_0
    have hbai : iW + signExtend12 (1 : BitVec 12) = baiW := by
      simp only [iW, baiW]
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      exact ofNat_addi1 i
    rw [hbai] at h
    exact h
  have e62C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 248) bvtProg 62
      (.ADDI .x15 .x21 (1 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e62_1
  have e62F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
      (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e62C
  have hpc62 : (B + 248) + 4 = AfterTeerSetup := by
    simp only [AfterTeerSetup]; bv_omega
  rw [hpc62] at e62F
  -- compose 57;;58;;59;;60;;61;;62
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e57F e58F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c01 e59F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c02 e60F
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c03 e61F
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c04 e62F
  change cpsTripleWithin
    ((((((1 + 1) + 1) + 1) + 1) + 1)) AfterBalCheck AfterTeerSetup
    bvtCode _ _ at c05
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c05

/-- Caller-private frame across teer. wordArray + s-regs; ambient tx/BAL
    ride in the callee footprint. -/
def loopTeerFrame (spC txBase outBase balBase chainIdW nW iW
    startW endW bodyLenW balLenW : Word)
    (csaved : Saved) (outVals : List Nat) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  wordArray outBase outVals **
  regOwn .x17
  -- x0 stays in the callee footprint (not framed) to avoid double-own.

theorem loopTeerFrame_pcFree (spC txBase outBase balBase chainIdW nW iW
    startW endW bodyLenW balLenW : Word)
    (csaved : Saved) (outVals : List Nat) :
    (loopTeerFrame spC txBase outBase balBase chainIdW nW iW
      startW endW bodyLenW balLenW csaved outVals).pcFree := by
  unfold loopTeerFrame savedFrame; bvt_pcf

set_option maxRecDepth 8000 in
/-- Teer success call (instr 63) under ambient-region `TeerAssumed`.
    Pre: full `bytesRegion txBase txBlob` + `bytesRegion balBase balBytes`.
    Post: a0 = teer APPLIED charge on slice `(txBlob.drop off).take len`. -/
theorem bvtIterTeerCall
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (spC txBase outBase balBase chainIdW nW bodyLenW : Word)
    (csaved : Saved) (txBlob balBytes : List (BitVec 8))
    (outVals : List Nat) (chainId i off len : Nat)
    (startW endW old1 : Word)
    (hentry : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hret : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hchain : chainIdW = BitVec.ofNat 64 chainId) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let balLenW := BitVec.ofNat 64 balBytes.length
    let baiW := BitVec.ofNat 64 (i + 1)
    let chargeW := BitVec.ofNat 64
      (teer ((txBlob.drop off).take len) balBytes chainId (i + 1))
    cpsTripleWithin (1 + nTeerSteps) AfterTeerSetup LinkTeer fullCode
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ balBase) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        loopTeerFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW balLenW csaved outVals)
      ((.x1 ↦ᵣ LinkTeer) **
        (.x10 ↦ᵣ chargeW) **
        regOwn .x11 **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        loopTeerFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW balLenW csaved outVals) := by
  intro iW txPtr txLenW balLenW baiW chargeW
  have hload : txPtr = txBase + BitVec.ofNat 64 off := by
    simp only [txPtr, hstart]
  have hlenW : txLenW = BitVec.ofNat 64 len := by
    simp only [txLenW, htxLen]
  have hflat0 := hteer.applied_flat LinkTeer txBase txPtr balBase balLenW
    chainIdW baiW txBlob balBytes off len chainId (i + 1)
    hret hbal hload hlen rfl hchain rfl
  have hflatLen : cpsTripleWithin nTeerSteps hteer.entry LinkTeer fullCode
      ((.x1 ↦ᵣ LinkTeer) ** (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ balBase) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion txBase txBlob ** bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkTeer) **
        (.x10 ↦ᵣ chargeW) **
        regOwn .x11 **
        bytesRegion txBase txBlob ** bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) := by
    simpa [hlenW, chargeW] using hflat0
  have hflatF := cpsTripleWithin_frameR
    (loopTeerFrame spC txBase outBase balBase chainIdW nW iW
      startW endW bodyLenW balLenW csaved outVals)
    (loopTeerFrame_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _) hflatLen
  have hcallee : cpsTripleWithin nTeerSteps hteer.entry LinkTeer fullCode
      ((.x1 ↦ᵣ LinkTeer) **
        ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
          (.x12 ↦ᵣ balBase) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion txBase txBlob **
          bytesRegion balBase balBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          loopTeerFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW balLenW csaved outVals))
      ((.x1 ↦ᵣ LinkTeer) **
        ((.x10 ↦ᵣ chargeW) **
          regOwn .x11 **
          bytesRegion txBase txBlob **
          bytesRegion balBase balBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          loopTeerFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW balLenW csaved outVals)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall := callWithin_spec AfterTeerSetup hteer.entry old1 teerJalOff
    nTeerSteps
    (by
      rw [hentry]
      show AfterTeerSetup + signExtend21 teerJalOff =
        (GuestAddrs.tx_eip7702_existing_authority_refund : Word)
      simp only [AfterTeerSetup, teerJalOff, B]
      decide)
    (fun a off' hi => bvt_mono a off'
      (CodeReq.ofProg_mem_at B AfterTeerSetup bvtProg 63
        (.JAL .x1 teerJalOff)
        (by simp only [AfterTeerSetup]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide) a off' hi))
    (by
      unfold loopTeerFrame savedFrame
      bvt_pcf)
    hcallee
  have hlink : AfterTeerSetup + 4 = LinkTeer := by
    simp only [AfterTeerSetup, LinkTeer]; bv_omega
  rw [hlink] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- Instr 64–68: SLLI/ADD/LD/ADD/SD — out[i] += teer charge.
    Pre: peeled cell at pureIntrinsic; post: cell = pureIntrinsic + charge. -/
theorem bvtIterStoreAdd
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8))
    (outPrefix outSuffix : List Nat) (balBytes : List (BitVec 8))
    (startW endW chargeW old5 old6 old7 : Word) (i : Nat)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    let pureW := BitVec.ofNat 64 pureIntrinsicStateGasSuccess
    let sumW := pureW + chargeW
    cpsTripleWithin 5 LinkTeer AfterStore bvtCode
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (outPtr ↦ₘ pureW) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArrayFrom outBase 0 outPrefix **
        wordArrayFrom outBase (i + 1) outSuffix **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) **
        (outPtr ↦ₘ sumW) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArrayFrom outBase 0 outPrefix **
        wordArrayFrom outBase (i + 1) outSuffix **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW outPtr pureW sumW
  -- 64 SLLI x5, x21, 3  (spec order: rs1 ** rd)
  have e64_0 := slli_spec_gen_within .x5 .x21 old5 iW (3 : BitVec 6)
    LinkTeer (by decide)
  have e64_1 : cpsTripleWithin 1 LinkTeer (LinkTeer + 4)
      (CodeReq.singleton LinkTeer (.SLLI .x5 .x21 (3 : BitVec 6)))
      ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ old5))
      ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i))) := by
    have h := e64_0
    have hs' : iW <<< (3 : BitVec 6).toNat = BitVec.ofNat 64 (8 * i) := by
      change iW <<< (3 : Nat) = BitVec.ofNat 64 (8 * i)
      simp only [iW]; exact slli3_ofNat i hi61
    rw [hs'] at h
    exact h
  have e64C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B LinkTeer bvtProg 64
      (.SLLI .x5 .x21 (3 : BitVec 6))
      (by simp only [LinkTeer]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e64_1
  -- Shared ambient across store (excludes focus regs of each step)
  let storeAmb : Assertion :=
    (.x10 ↦ᵣ chargeW) ** (.x19 ↦ᵣ outBase) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have hstoreAmb : storeAmb.pcFree := by
    unfold storeAmb savedFrame
    repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_wordArrayFrom outBase 0 outPrefix
      | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix
  have e64F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) ** (outPtr ↦ₘ pureW) ** storeAmb)
    (by
      apply pcFree_sepConj pcFree_regIs
      apply pcFree_sepConj pcFree_regIs
      apply pcFree_sepConj pcFree_memIs
      exact hstoreAmb) e64C
  have hpc64 : LinkTeer + 4 = B + 260 := by
    simp only [LinkTeer]; bv_omega
  rw [hpc64] at e64F
  -- 65 ADD x6, x19, x5 → x6 = outPtr
  have e65_0 := add_spec_gen_within .x6 .x19 .x5 outBase
    (BitVec.ofNat 64 (8 * i)) old6 (B + 260) (by decide)
  have e65_1 : cpsTripleWithin 1 (B + 260) ((B + 260) + 4)
      (CodeReq.singleton (B + 260) (.ADD .x6 .x19 .x5))
      ((.x19 ↦ᵣ outBase) ** (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ old6))
      ((.x19 ↦ᵣ outBase) ** (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr)) := by
    have h := e65_0
    have heq : outBase + BitVec.ofNat 64 (8 * i) = outPtr := by
      simp only [outPtr]
    rw [heq] at h
    exact h
  have e65C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 260) bvtProg 65
      (.ADD .x6 .x19 .x5)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e65_1
  have e65F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ iW) ** (.x7 ↦ᵣ old7) ** (outPtr ↦ₘ pureW) **
      (.x10 ↦ᵣ chargeW) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e65C
  have hpc65 : (B + 260) + 4 = B + 264 := by bv_omega
  rw [hpc65] at e65F
  -- 66 LD x7, 0(x6)
  have e66_0 := ld_spec_gen_within .x7 .x6 outPtr old7 pureW
    (0 : BitVec 12) (B + 264) (by decide)
  have e66_1 : cpsTripleWithin 1 (B + 264) ((B + 264) + 4)
      (CodeReq.singleton (B + 264) (.LD .x7 .x6 (0 : BitVec 12)))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ old7) ** (outPtr ↦ₘ pureW))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ pureW) ** (outPtr ↦ₘ pureW)) := by
    have h := e66_0
    have hoff : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      simp
    rw [hoff] at h
    exact h
  have e66C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 264) bvtProg 66
      (.LD .x7 .x6 (0 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e66_1
  have e66F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
      (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e66C
  have hpc66 : (B + 264) + 4 = B + 268 := by bv_omega
  rw [hpc66] at e66F
  -- 67 ADD x7, x7, x10
  have e67_0 := add_spec_gen_rd_eq_rs1_within .x7 .x10 pureW chargeW
    (B + 268) (by decide)
  have e67_1 : cpsTripleWithin 1 (B + 268) ((B + 268) + 4)
      (CodeReq.singleton (B + 268) (.ADD .x7 .x7 .x10))
      ((.x7 ↦ᵣ pureW) ** (.x10 ↦ᵣ chargeW))
      ((.x7 ↦ᵣ sumW) ** (.x10 ↦ᵣ chargeW)) := by
    have h := e67_0
    change cpsTripleWithin 1 (B + 268) ((B + 268) + 4) _
      ((.x7 ↦ᵣ pureW) ** (.x10 ↦ᵣ chargeW))
      ((.x7 ↦ᵣ (pureW + chargeW)) ** (.x10 ↦ᵣ chargeW)) at h
    simpa only [sumW] using h
  have e67C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 268) bvtProg 67
      (.ADD .x7 .x7 .x10)
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e67_1
  have e67F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
      (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) ** (.x6 ↦ᵣ outPtr) **
      (outPtr ↦ₘ pureW) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e67C
  have hpc67 : (B + 268) + 4 = B + 272 := by bv_omega
  rw [hpc67] at e67F
  -- 68 SD x6, x7, 0
  have e68_0 := sd_spec_gen_within .x6 .x7 outPtr sumW pureW
    (0 : BitVec 12) (B + 272)
  have e68_1 : cpsTripleWithin 1 (B + 272) ((B + 272) + 4)
      (CodeReq.singleton (B + 272) (.SD .x6 .x7 (0 : BitVec 12)))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ pureW))
      ((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ sumW)) := by
    have h := e68_0
    have hoff : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      simp
    rw [hoff] at h
    exact h
  have e68C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 272) bvtProg 68
      (.SD .x6 .x7 (0 : BitVec 12))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e68_1
  have e68F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
      (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArrayFrom outBase 0 outPrefix **
      wordArrayFrom outBase (i + 1) outSuffix **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by
      unfold savedFrame
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_wordArrayFrom outBase 0 outPrefix
        | exact pcFree_wordArrayFrom outBase (i + 1) outSuffix) e68C
  have hpc68 : (B + 272) + 4 = AfterStore := by
    simp only [AfterStore]; bv_omega
  rw [hpc68] at e68F
  -- Compose 64;;65;;66;;67;;68
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e64F e65F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c01 e66F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c02 e67F
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c03 e68F
  change cpsTripleWithin ((((1 + 1) + 1) + 1) + 1) LinkTeer AfterStore
    bvtCode _ _ at c04
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c04

set_option maxRecDepth 8000 in
/-- Instr 69: JAL +12 → LoopAdvance (skip zero-store join). -/
theorem bvtIterAfterStoreJal
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW iW chargeW : Word)
    (v5 v6 v7 : Word) :
    cpsTripleWithin 1 AfterStore LoopAdvance bvtCode
      ((.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have e69_0 := jal_x0_spec_gen_within (12 : BitVec 21) AfterStore
  have e69C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterStore bvtProg 69
      (.JAL .x0 (12 : BitVec 21))
      (by simp only [AfterStore]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e69_0
  have hpc : AfterStore + signExtend21 (12 : BitVec 21) = LoopAdvance := by
    simp only [AfterStore, LoopAdvance]
    rw [show signExtend21 (12 : BitVec 21) = (12 : Word) from by decide]
    bv_omega
  rw [hpc] at e69C
  let ambient : Assertion :=
    (.x21 ↦ᵣ iW) **
      (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have e69 : cpsTripleWithin 1 AfterStore LoopAdvance bvtCode ambient ambient := by
    have h0 := cpsTripleWithin_frameR ambient
      (by unfold ambient savedFrame; bvt_pcf) e69C
    exact cpsTripleWithin_weaken
      (fun h hp => by
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      h0
  exact e69

/-! ## wordArray peel helper for intrinsic + store glue -/

/-- Peel cell `i` when its value is already `v` (e.g. pureIntrinsic after write). -/
theorem wordArray_set_eq_of_get
    (base : Word) (outVals : List Nat) (i v : Nat)
    (hi : i < outVals.length) (hcell : outVals[i] = v) :
    wordArray base outVals =
      (wordArrayFrom base 0 (outVals.take i) **
        ((base + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 v) **
        wordArrayFrom base (i + 1) (outVals.drop (i + 1))) := by
  have h := wordArray_split base outVals i hi
  simpa [hcell] using h

/-- Peel form of `wordArray` after `List.set i newV`. -/
theorem wordArray_of_set
    (base : Word) (outVals : List Nat) (i newV : Nat)
    (hi : i < outVals.length) :
    wordArray base (outVals.set i newV) =
      (wordArrayFrom base 0 (outVals.take i) **
        ((base + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 newV) **
        wordArrayFrom base (i + 1) (outVals.drop (i + 1))) := by
  have hi' : i < (outVals.set i newV).length := by simpa using hi
  have h := wordArray_split base (outVals.set i newV) i hi'
  have hget : (outVals.set i newV)[i] = newV := List.getElem_set_self hi'
  have htake : (outVals.set i newV).take i = outVals.take i := by
    rw [List.take_set, List.set_eq_of_length_le]
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hdrop : (outVals.set i newV).drop (i + 1) = outVals.drop (i + 1) := by
    rw [List.drop_set, if_pos (Nat.lt_succ_self i)]
  simpa [hget, htake, hdrop] using h

set_option maxRecDepth 8000 in
/-- Store under full wordArray when cell i is pureIntrinsic: writes pure+charge
    and folds to `outVals.set i newV`. Requires `chargeW = ofNat chargeNat` and
    no BitVec wrap on pure+charge (= charge when pure=0). -/
theorem bvtIterStoreAdd_fold
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8))
    (startW endW chargeW old5 old6 old7 : Word) (i chargeNat : Nat)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess)
    (_hcharge : chargeW = BitVec.ofNat 64 chargeNat)
    (hsum : BitVec.ofNat 64 pureIntrinsicStateGasSuccess + chargeW =
      BitVec.ofNat 64 (pureIntrinsicStateGasSuccess + chargeNat))
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    let pureW := BitVec.ofNat 64 pureIntrinsicStateGasSuccess
    let sumW := pureW + chargeW
    let outVals' := outVals.set i (pureIntrinsicStateGasSuccess + chargeNat)
    cpsTripleWithin 5 LinkTeer AfterStore bvtCode
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        wordArray outBase outVals **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) **
        wordArray outBase outVals' **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW outPtr pureW sumW outVals'
  have hpeel := wordArray_set_eq_of_get outBase outVals i
    pureIntrinsicStateGasSuccess hi hcell
  have hfold := wordArray_of_set outBase outVals i
    (pureIntrinsicStateGasSuccess + chargeNat) hi
  have hstore := bvtIterStoreAdd spC txBase outBase balBase chainIdW nW
    csaved txBlob (outVals.take i) (outVals.drop (i + 1)) balBytes
    startW endW chargeW old5 old6 old7 i hi61
  -- Align sumW in store post with ofNat (pure+charge) via hsum
  have hstore' : cpsTripleWithin 5 LinkTeer AfterStore bvtCode
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (outPtr ↦ₘ pureW) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArrayFrom outBase 0 (outVals.take i) **
        wordArrayFrom outBase (i + 1) (outVals.drop (i + 1)) **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) **
        (outPtr ↦ₘ (BitVec.ofNat 64 (pureIntrinsicStateGasSuccess + chargeNat))) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArrayFrom outBase 0 (outVals.take i) **
        wordArrayFrom outBase (i + 1) (outVals.drop (i + 1)) **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
    have h := hstore
    -- rewrite sumW cell via hsum
    simpa [sumW, pureW, hsum] using h
  refine cpsTripleWithin_weaken ?_ ?_ hstore'
  · intro h hp
    rw [hpeel] at hp
    xperm_hyp hp
  · intro h hq
    rw [hfold]
    xperm_hyp hq

set_option maxRecDepth 8000 in
/-- Intrinsic when `outVals[i] = pureIntrinsic`: ambient wordArray is preserved
    (peel → write same value → fold). AfterEndSpan → LinkIntrinsic. -/
theorem bvtIterIntrinsic_preserveCell
    (hintr : IntrinsicAssumed fullCode)
    (spC txBase outBase balBase chainIdW nW bodyLenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool)
    (i off len : Nat) (startW endW old1 : Word)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hret : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin (1 + nIntrinsicSteps) AfterEndSpan LinkIntrinsic fullCode
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes balEnabled)
      ((.x1 ↦ᵣ LinkIntrinsic) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes balEnabled) := by
  intro iW txPtr txLenW outPtr
  have hpeel := wordArray_set_eq_of_get outBase outVals i
    pureIntrinsicStateGasSuccess hi hcell
  have hcall := bvtIterIntrinsic hintr spC txBase outBase balBase chainIdW nW
    bodyLenW csaved txBlob balBytes balEnabled i off len startW endW
    (BitVec.ofNat 64 pureIntrinsicStateGasSuccess) old1 hentry hret hstart hlen htxLen
  have hfr := cpsTripleWithin_frameR
    (wordArrayFrom outBase 0 (outVals.take i) **
      wordArrayFrom outBase (i + 1) (outVals.drop (i + 1)))
    (by
      apply pcFree_sepConj
      · exact pcFree_wordArrayFrom outBase 0 (outVals.take i)
      · exact pcFree_wordArrayFrom outBase (i + 1) (outVals.drop (i + 1)))
    hcall
  -- Expand wordArray in hyp pre/post, then xperm into framed peel form.
  refine cpsTripleWithin_weaken ?_ ?_ hfr
  · intro h hp
    rw [hpeel] at hp
    xperm_hyp hp
  · intro h hq
    -- framed post → full wordArray post: expand goal, then xperm
    rw [hpeel]
    xperm_hyp hq

set_option maxRecDepth 8000 in
/-- bal=0 success half-iter from AfterEndSpan: intrinsic (preserve cell) +
    BNE/BEQ/i++/back-edge → LoopGuard at i+1. Requires balBase=0. -/
theorem bvtIterBal0FromIntrinsic
    (hintr : IntrinsicAssumed fullCode)
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8))
    (i off len : Nat) (startW endW old1 : Word)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hret : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess) :
    let iW := BitVec.ofNat 64 i
    let bodyLenW := BitVec.ofNat 64 txBlob.length
    let balBase : Word := 0
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin ((1 + nIntrinsicSteps) + 4) AfterEndSpan LoopGuard fullCode
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes false)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW bodyLenW balBase txPtr txLenW outPtr
  have hintrP := bvtIterIntrinsic_preserveCell hintr spC txBase outBase balBase
    chainIdW nW bodyLenW csaved txBlob outVals balBytes false i off len
    startW endW old1 hentry hret hstart hlen htxLen hi hcell
  have htail := bvtIterBal0Tail spC txBase outBase chainIdW nW csaved txBlob
    outVals balBytes i startW endW
  have htailF : cpsTripleWithin 4 LinkIntrinsic LoopGuard fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          (BitVec.ofNat 64 balBytes.length) startW endW iW)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
    have h0 := cpsTripleWithin_extend_code bvt_mono htail
    exact cpsTripleWithin_weaken (fun _ hp => by
        unfold bal0Rest at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by
      -- preserveCell post → bal0Tail pre (balBase=0, no BAL region)
      unfold loopIntrinsicFrame at hq
      simp only [balBase, Bool.false_eq_true, ↓reduceIte] at hq
      -- cancel trailing empAssertion from balEnabled=false
      have hq' :
          ((.x1 ↦ᵣ LinkIntrinsic) **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBlob **
            wordArray outBase outVals **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ (0 : Word)) **
            (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            regOwn .x17 ** savedFrame spC csaved) h := by
        -- hq ends with ** empAssertion; cancel
        simpa [sepConj_emp_right'] using hq
      unfold bal0Rest
      xperm_hyp hq')
    hintrP htailF

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
