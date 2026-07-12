/-
  Shared declaration home for the ADDMOD zero arm, dispatch, and result stack.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryLdChain
import EvmAsm.Evm64.AddMod.LimbSpec

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

-- ============================================================================
-- Arm 1: the zero branch (byte 844 → 864)
-- ============================================================================

/-- Frame carried through `phase2_zero_path` (which touches only `x12` and the
    four result cells at F+32..56): `x5`, the truncated-sum cells at F+0..24,
    the S1/S2 park cells, and the full La tail (registers + S3 + scratch band). -/
def addmodZeroArmFrame (F x5Old r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  (.x5 ↦ᵣ x5Old) **
  ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
  ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
  ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
  ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
  ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
  addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem

theorem addmodZeroArmFrame_pcFree
    (F x5Old r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (addmodZeroArmFrame F x5Old r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
      x1v x2v x6v x7v x9v x10v x11v
      sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  unfold addmodZeroArmFrame addmodLaTail addmodLaRegTail addmodLaScratchTail
    divScratchValuesCallNoX1
  pcFree

/-- **The ADDMOD zero branch** (byte 844 → 864, over `C`): when `N = 0`, the
    zero path stores `0` into the result cells and the epilogue advances the
    stack pointer, landing `EvmWord.addmod a b 0 = 0` at `sp+64`
    (`addmodLdResultOwned`), with everything else shed to owned. -/
theorem evm_addmod_zero_branch_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (a b : EvmWord)
    (hn0 : n0 = 0) (hn1 : n1 = 0) (hn2 : n2 = 0) (hn3 : n3 = 0) :
    cpsTripleWithin (4 + 1) (bt + 844) (bt + 864)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodLdResultOwned F
        (EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3]))) := by
  have hres : EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3]) = 0 := by
    subst hn0 hn1 hn2 hn3
    rw [show EvmWord.fromLimbs ![(0 : Word), 0, 0, 0] = (0 : EvmWord) from by decide]
    exact EvmWord.addmod_zero a b
  -- zero_path (844 → 860), framed + over C
  have hz := carry_block_in_C
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun ad i h => evm_addmod_total_program_code_zero_path_sub ad i h)
    (cpsTripleWithin_frameR
      (addmodZeroArmFrame F x5Old r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
        x1v x2v x6v x7v x9v x10v x11v
        sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodZeroArmFrame_pcFree F x5Old r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
        x1v x2v x6v x7v x9v x10v x11v
        sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (evm_addmod_phase2_zero_path_ofProg_spec_within F n0 n1 n2 n3 (bt + 844)))
  rw [show (bt + 844) + 16 = bt + 860 from by bv_omega] at hz
  -- epilogue (860 → 864), framed + over C
  have he0 := evm_addmod_epilogue_spec_within F (bt + 860)
  simp only at he0
  have he := carry_block_in_C
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun ad i h => evm_addmod_total_program_code_epilogue_sub ad i h)
    (cpsTripleWithin_frameR
      (((F + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((F + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((F + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((F + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word)) **
       addmodZeroArmFrame F x5Old r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
         x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (by
        unfold addmodZeroArmFrame addmodLaTail addmodLaRegTail addmodLaScratchTail
          divScratchValuesCallNoX1
        pcFree)
      he0)
  rw [show (bt + 860) + 4 = bt + 864 from by bv_omega] at he
  refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post)
    (cpsTripleWithin_seq_perm_same_cr ?mid hz he)
  case mid =>
    intro h hp
    xperm_hyp hp
  case pre =>
    simp only [addmodZeroArmFrame, sepConj_assoc'] at hp ⊢
    xperm_hyp hp
  case post =>
    rw [hres]
    have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
    have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
    have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
    have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
    have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
    have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
    have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
    have g0 : (0 : EvmWord).getLimbN 0 = (0 : Word) := by decide
    have g1 : (0 : EvmWord).getLimbN 1 = (0 : Word) := by decide
    have g2 : (0 : EvmWord).getLimbN 2 = (0 : Word) := by decide
    have g3 : (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
    simp only [addmodLdResultOwned, addmodZeroArmFrame,
      addmodLaTail, addmodLaRegTail, addmodLaScratchTail,
      evmWordIs, evmWordOwn, g0, g1, g2, g3,
      e0, e8, e16, e24, e32, e40, e48, e56,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero, sepConj_assoc'] at hq ⊢
    exact sepConj_mono (fun _ x => x)                                 -- x12
      (sepConj_mono (fun _ x => x)                                    -- res0
      (sepConj_mono (fun _ x => x)                                    -- res1
      (sepConj_mono (fun _ x => x)                                    -- res2
      (sepConj_mono (fun _ x => x)                                    -- res3
      (sepConj_mono (regIs_implies_regOwn .x0)
      (sepConj_mono (regIs_implies_regOwn .x1)
      (sepConj_mono (regIs_implies_regOwn .x2)
      (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
      (sepConj_mono (regIs_implies_regOwn .x9)
      (sepConj_mono (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x11)
      (sepConj_mono (divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
        F dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (sepConj_mono memIs_implies_memOwn                              -- F−160
      (sepConj_mono memIs_implies_memOwn                              -- evmWordOwn F
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn                              -- S2 (3872..)
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn                              -- S3 (3840..)
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn                              -- S1 (3904..)
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        memIs_implies_memOwn))))))))))))))))))))))))))))))
      h (by xperm_hyp hq)

-- ============================================================================
-- Arm 2: the no-carry branch (byte 836 → 864)
-- ============================================================================

/-- **The ADDMOD no-carry branch** (byte 836 → 864, over `C`): when `N ≠ 0`
    and the 257th carry bit is clear, the truncated sum `r = a + b` is exact,
    so a single MOD near-call reduces it and the exit JAL jumps to the join;
    `EvmWord.mod (a+b) N = EvmWord.addmod a b N` by
    `mod_truncated_sum_eq_addmod_of_no_overflow`. Lands the same
    `addmodLdResultOwned` post as the other two arms. -/
theorem evm_addmod_no_carry_branch_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (a b : EvmWord)
    (hr : EvmWord.fromLimbs ![r0, r1, r2, r3] = a + b)
    (hnc : (EvmWord.addCarry a b).fst = false)
    (hoffsetNC : (bt + 836) + signExtend21 moNC = calleeEntry)
    (callerAlignNC : ((bt + 836) + 4) &&& ~~~(1 : Word) = (bt + 836) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisjNC : (CodeReq.singleton (bt + 836) (.JAL .x1 moNC)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin ((1 + (unifiedDivBound + 1)) + 1) (bt + 836) (bt + 864)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodLdResultOwned F
        (EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3]))) := by
  have hno : a.toNat + b.toNat < 2 ^ 256 := by
    simp only [EvmWord.addCarry, decide_eq_false_iff_not, not_le] at hnc
    exact hnc
  have hres : EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3])
        (EvmWord.fromLimbs ![n0, n1, n2, n3])
      = EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3]) := by
    rw [hr]
    exact EvmWord.mod_truncated_sum_eq_addmod_of_no_overflow a b _ hno
  -- the MOD near-call over C (836 → 840)
  have hjalSub : ∀ ad i, CodeReq.singleton (bt + 836) (.JAL .x1 moNC) ad = some i →
      (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC) ad = some i := by
    intro ad i ha
    refine evm_addmod_total_program_code_nc_mod_call_sub ad i ?_
    rw [show CodeReq.ofProg (bt + 836) (evm_addmod_phase2_mod_call moNC)
        = CodeReq.singleton (bt + 836) (.JAL .x1 moNC) from CodeReq.ofProg_singleton]
    exact ha
  have hcall := cpsTripleWithin_extend_code
    (CodeReq.union_sub
      (fun ad i ha => CodeReq.union_mono_left ad i (hjalSub ad i ha))
      (CodeReq.mono_union_right hdisjTC (fun _ _ h => h)))
    (evm_addmod_v5_call_adapter (bt + 836) F calleeEntry moNC
      (EvmWord.fromLimbs ![r0, r1, r2, r3]) (EvmWord.fromLimbs ![n0, n1, n2, n3])
      x9v x1v x2v x5Old x6v x7v x10v x11v
      dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hoffsetNC callerAlignNC retAlign hdisjNC)
  have hcallF := cpsTripleWithin_frameR
    (addmodCall1Frame F sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3)
    (addmodCall1Frame_pcFree F sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3)
    hcall
  rw [show (bt + 836) + 4 = bt + 840 from by bv_omega] at hcallF
  -- the exit JAL over C (840 → 864), with everything framed
  have hjal := jal_x0_spec_gen_within 24 (bt + 840)
  rw [show (bt + 840) + signExtend21 (24 : BitVec 21) = bt + 864 from by
    rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by decide]
    bv_omega] at hjal
  have hjalC := carry_block_in_C
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun ad i h => evm_addmod_total_program_code_nc_exit_jal_sub ad i (by
      rw [show CodeReq.ofProg (bt + 840) (JAL .x0 24)
          = CodeReq.singleton (bt + 840) (.JAL .x0 24) from CodeReq.ofProg_singleton]
      exact h))
    hjal
  have hjalF := cpsTripleWithin_frameR
    ((modStackDispatchPostCallableX9Owned F (EvmWord.fromLimbs ![r0, r1, r2, r3])
        (EvmWord.fromLimbs ![n0, n1, n2, n3]) (bt + 840) **
      memOwn (F + signExtend12 (3936 : BitVec 12))) **
     addmodCall1Frame F sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3)
    (by
      rw [modStackDispatchPostCallableX9Owned_unfold, modStackDispatchPostCallable_unfold,
        divScratchOwnCallNoX1_unfold, divScratchOwn_unfold]
      unfold addmodCall1Frame evmWordIs
      pcFree)
    hjalC
  refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post)
    (cpsTripleWithin_seq_perm_same_cr ?mid hcallF hjalF)
  case mid =>
    intro h hp
    exact (sepConj_emp_left h).mpr hp
  case pre =>
    have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
    have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
    have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
    have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
    have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
    have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
    have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
    simp only [addmodLaTail, addmodLaRegTail, addmodLaScratchTail,
      addmodCall1Frame, divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold,
      evmWordIs, EvmWord.getLimbN_fromLimbs_gen_0, EvmWord.getLimbN_fromLimbs_gen_1,
      EvmWord.getLimbN_fromLimbs_gen_2, EvmWord.getLimbN_fromLimbs_gen_3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      e0, e8, e16, e24, e32, e40, e48, e56,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp ⊢
    xperm_hyp hp
  case post =>
    have hq' := (sepConj_emp_left h).mp hq
    rw [← hres]
    simp only [addmodLdResultOwned, addmodCall1Frame,
      modStackDispatchPostCallableX9Owned_unfold, modStackDispatchPostCallable_unfold,
      sepConj_assoc'] at hq' ⊢
    exact sepConj_mono (fun _ x => x)                                 -- x12
      (sepConj_mono (fun _ x => x)                                    -- result word
      (sepConj_mono (regIs_implies_regOwn .x0)
      (sepConj_mono (regIs_implies_regOwn .x1)
      (sepConj_mono (fun _ x => x)                                    -- regOwn x2
      (sepConj_mono (fun _ x => x)                                    -- regOwn x5
      (sepConj_mono (fun _ x => x)                                    -- regOwn x6
      (sepConj_mono (fun _ x => x)                                    -- regOwn x7
      (sepConj_mono (fun _ x => x)                                    -- regOwn x9
      (sepConj_mono (fun _ x => x)                                    -- regOwn x10
      (sepConj_mono (fun _ x => x)                                    -- regOwn x11
      (sepConj_mono (fun _ x => x)                                    -- divScratch
      (sepConj_mono (fun _ x => x)                                    -- memOwn F−160
      (sepConj_mono (fun _ hw => evmWordIs_to_evmWordOwn
        (addr := F) (v := EvmWord.fromLimbs ![r0, r1, r2, r3]) hw)    -- evmWordOwn F
      (sepConj_mono memIs_implies_memOwn                              -- S2 (3872..)
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn                              -- S3 (3840..)
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn                              -- S1 (3904..)
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        memIs_implies_memOwn))))))))))))))))))))))))
      h (by xperm_hyp hq')

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

-- ============================================================================
-- Pure helpers: the OR-fold N-zero test vs the fromLimbs modulus
-- ============================================================================

/-- If the 4-limb OR-fold is zero, every limb is zero. -/
theorem or4_eq_zero {n0 n1 n2 n3 : Word}
    (h : n0 ||| n1 ||| n2 ||| n3 = 0) :
    n0 = 0 ∧ n1 = 0 ∧ n2 = 0 ∧ n3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i _
    have hb := congrArg (fun w => BitVec.getLsbD w i) h
    simp only [BitVec.getLsbD_or] at hb
    rw [show BitVec.getLsbD (0 : Word) i = false from by simp] at hb ⊢
    rcases Bool.or_eq_false_iff.mp hb with ⟨h012, h3⟩
    rcases Bool.or_eq_false_iff.mp h012 with ⟨h01, h2⟩
    rcases Bool.or_eq_false_iff.mp h01 with ⟨h0, h1⟩
    first | exact h0 | exact h1 | exact h2 | exact h3

/-- If the 4-limb OR-fold is nonzero, the assembled modulus is nonzero. -/
theorem fromLimbs_ne_zero_of_or4 {n0 n1 n2 n3 : Word}
    (h : ¬(n0 ||| n1 ||| n2 ||| n3 = 0)) :
    EvmWord.fromLimbs ![n0, n1, n2, n3] ≠ 0 := by
  intro hzero
  apply h
  have h0 : n0 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 0) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_0] using this
  have h1 : n1 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 1) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_1] using this
  have h2 : n2 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 2) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_2] using this
  have h3 : n3 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 3) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_3] using this
  rw [h0, h1, h2, h3]
  decide

-- ============================================================================
-- Dispatch prefix: prologue ;; phase1_carry (byte 0 → 124) over C
-- ============================================================================

/-- The 257-bit overflow bit of `a + b` (the value `evm_add` leaves in `x5`,
    folded via `evm_add_stack_carry3_eq_overflow`). -/
def addmodOverflowBit (a b : EvmWord) : Word :=
  if a.toNat + b.toNat ≥ 2 ^ 256 then (1 : Word) else 0

/-- The dispatch prefix over `C`: the 4-limb add prologue followed by the
    carry-parking `MV x7, x5`. Lands `x12 = sp+32`, the truncated sum at
    `sp+32..56`, the overflow bit in `x5` AND `x7` (the latter with the raw
    `+ signExtend12 0` shape phase1 produces), `x11` at the limb-3 partial
    carry, and `x6` shed to owned (its junk carry-chain value dies at the
    N-zero test). -/
theorem evm_addmod_dispatch_prefix_spec_within
    (bt sp : Word) (x5v x6v x7v x11v : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (a b : EvmWord) :
    cpsTripleWithin (30 + 1) bt (bt + 124)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ x7v) ** (.x6 ↦ᵣ x6v) ** (.x5 ↦ᵣ x5v) **
       (.x11 ↦ᵣ x11v) ** evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x6 **
       (.x5 ↦ᵣ addmodOverflowBit a b) **
       (.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12))) **
       (.x11 ↦ᵣ (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3)
                 then (1 : Word) else 0)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b)) := by
  -- prologue over C (bt → bt+120)
  have hprol := carry_block_in_C
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun ad i h => evm_addmod_total_program_code_prologue_sub ad i h)
    (evm_addmod_prologue_stack_named_spec_within sp bt a b x7v x6v x5v x11v)
  -- phase1 over C (bt+120 → bt+124), with the dead incoming x7 owned
  have hph1 : cpsTripleWithin 1 (bt + 120) ((bt + 120) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (regOwn .x7 ** (.x5 ↦ᵣ addmodOverflowBit a b))
      ((.x5 ↦ᵣ addmodOverflowBit a b) **
       (.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)))) := by
    refine cpsTripleWithin_pre_regOwn (fun vOld => ?_)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (carry_block_in_C
        (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
        (calleeCode := evm_mod_callable_code_v5 calleeEntry)
        (fun ad i h => evm_addmod_total_program_code_phase1_carry_sub ad i h)
        (evm_addmod_phase1_carry_spec_within (addmodOverflowBit a b) vOld (bt + 120)))
  rw [show (bt + 120) + 4 = bt + 124 from by bv_omega] at hph1
  -- frame phase1 with everything it does not touch
  have hph1F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x6 **
     (.x11 ↦ᵣ (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3)
               then (1 : Word) else 0)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (a + b))
    (by unfold evmWordIs; pcFree)
    hph1
  -- the carry3 chain the prologue leaves in x5 equals the overflow bit
  have hov := evm_add_stack_carry3_eq_overflow a b
  simp only at hov
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?post)
    (cpsTripleWithin_seq_perm_same_cr ?mid hprol hph1F)
  case mid =>
    intro h hp
    simp only [evmAddModPrologueStackPost_unfold] at hp
    rw [hov] at hp
    rw [show (if a.toNat + b.toNat ≥ 2 ^ 256 then (1 : Word) else 0)
        = addmodOverflowBit a b from rfl] at hp
    exact sepConj_mono
      (sepConj_mono (regIs_implies_regOwn .x7) (fun _ x => x))
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x6)
          (fun _ x => x)))
      h (by xperm_hyp hp)
  case post =>
    xperm_hyp hq

-- ============================================================================
-- The ADDMOD dispatch entry state and the post-prefix frame
-- ============================================================================

/-- The full ADDMOD dispatch entry state (byte 0): `x12 = sp`, the operands
    `a`/`b` on the EVM stack and the modulus limbs at `sp+64..88`, generic
    dispatcher registers, the S1/S2/S3 park cells, and the MOD-callable
    scratch cells below `sp` (the band's top four cells at `sp..sp+24` are
    the `a` word itself). All cells are stated relative `F = sp + 32`, the
    post-prologue frame pointer, to match the branch-arm preconditions. -/
def addmodTotalEntry (sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) **
  (.x5 ↦ᵣ x5v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) ** (.x9 ↦ᵣ x9v) **
  (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  (((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
  (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
  (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
  (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
  (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
  (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
  (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
  (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
  (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
  (((sp + 32) + signExtend12 (4056 : BitVec 12)) ↦ₘ u0) **
  (((sp + 32) + signExtend12 (4048 : BitVec 12)) ↦ₘ u1) **
  (((sp + 32) + signExtend12 (4040 : BitVec 12)) ↦ₘ u2) **
  (((sp + 32) + signExtend12 (4032 : BitVec 12)) ↦ₘ u3) **
  (((sp + 32) + signExtend12 (4024 : BitVec 12)) ↦ₘ u4) **
  (((sp + 32) + signExtend12 (4016 : BitVec 12)) ↦ₘ u5) **
  (((sp + 32) + signExtend12 (4008 : BitVec 12)) ↦ₘ u6) **
  (((sp + 32) + signExtend12 (4000 : BitVec 12)) ↦ₘ u7) **
  (((sp + 32) + signExtend12 (3992 : BitVec 12)) ↦ₘ shiftMem) **
  (((sp + 32) + signExtend12 (3984 : BitVec 12)) ↦ₘ nMem) **
  (((sp + 32) + signExtend12 (3976 : BitVec 12)) ↦ₘ jMem) **
  (((sp + 32) + signExtend12 (3968 : BitVec 12)) ↦ₘ retMem) **
  (((sp + 32) + signExtend12 (3960 : BitVec 12)) ↦ₘ dMem) **
  (((sp + 32) + signExtend12 (3952 : BitVec 12)) ↦ₘ dloMem) **
  (((sp + 32) + signExtend12 (3944 : BitVec 12)) ↦ₘ scratch_un0) **
  (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)

theorem addmodTotalEntry_pcFree (sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) :
    (addmodTotalEntry sp x1v x2v x5v x6v x7v x9v x10v x11v a b
      n0 n1 n2 n3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem).pcFree := by
  unfold addmodTotalEntry evmWordIs
  pcFree

/-- Everything the N-zero test does not touch, in the post-prefix state:
    the untouched dispatcher registers, `x7`/`x11` at their post-prefix
    values, the `a` word and the truncated sum, and all park/scratch cells. -/
def addmodPostPrefixRest (sp : Word)
    (x1v x2v x9v x10v : Word) (a b : EvmWord)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) : Assertion :=
  (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) **
  (.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12))) **
  (.x11 ↦ᵣ (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3)
            then (1 : Word) else 0)) **
  evmWordIs (sp + 32) (a + b) **
  (((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
  (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
  (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
  (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
  (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
  (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
  (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
  (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
  (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
  divScratchValuesCallNoX1 (sp + 32)
    (a.getLimbN 3) (a.getLimbN 2) (a.getLimbN 1) (a.getLimbN 0)
    u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
  (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)

theorem addmodPostPrefixRest_pcFree (sp : Word)
    (x1v x2v x9v x10v : Word) (a b : EvmWord)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) :
    (addmodPostPrefixRest sp x1v x2v x9v x10v a b
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem).pcFree := by
  unfold addmodPostPrefixRest evmWordIs
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  pcFree

/-- The N-zero-test post cells (common to both branch targets), at `F = sp+32`:
    the OR-fold in `x6`, the last modulus limb in `x5`, and the modulus cells. -/
def addmodNZeroCells (sp : Word) (n0 n1 n2 n3 : Word) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** (.x6 ↦ᵣ (n0 ||| n1 ||| n2 ||| n3)) ** (.x5 ↦ᵣ n3) **
  (.x0 ↦ᵣ (0 : Word)) **
  (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3)

/-- Dispatch prefix + N-zero test as a two-way branch over `C` (byte 0 →
    {844 with `N = 0`, 156 with `N ≠ 0`}), from the full ADDMOD entry. The
    pure branch fact leads each target post so the dead arm is refutable by
    direct destructuring. -/
theorem evm_addmod_dispatch_branch_spec_within
    (bt sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsBranchWithin ((30 + 1) + 8) bt
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (addmodTotalEntry sp x1v x2v x5v x6v x7v x9v x10v x11v a b
        n0 n1 n2 n3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
        u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
        scratch_un0 scratchMem)
      (bt + 844)
        ((⌜n0 ||| n1 ||| n2 ||| n3 = 0⌝ ** addmodNZeroCells sp n0 n1 n2 n3) **
         addmodPostPrefixRest sp x1v x2v x9v x10v a b
           sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
           u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
           scratch_un0 scratchMem)
      (bt + 156)
        ((⌜¬(n0 ||| n1 ||| n2 ||| n3 = 0)⌝ ** addmodNZeroCells sp n0 n1 n2 n3) **
         addmodPostPrefixRest sp x1v x2v x9v x10v a b
           sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
           u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
           scratch_un0 scratchMem) := by
  -- the prefix, framed with the untouched remainder of the entry
  have hpre := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) **
     (.x10 ↦ᵣ x10v) **
     (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
     (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
     (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
     (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
     (((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
     (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
     (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
     (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
     (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
     (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
     (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
     (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
     (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
     (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
     (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
     (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
     (((sp + 32) + signExtend12 (4056 : BitVec 12)) ↦ₘ u0) **
     (((sp + 32) + signExtend12 (4048 : BitVec 12)) ↦ₘ u1) **
     (((sp + 32) + signExtend12 (4040 : BitVec 12)) ↦ₘ u2) **
     (((sp + 32) + signExtend12 (4032 : BitVec 12)) ↦ₘ u3) **
     (((sp + 32) + signExtend12 (4024 : BitVec 12)) ↦ₘ u4) **
     (((sp + 32) + signExtend12 (4016 : BitVec 12)) ↦ₘ u5) **
     (((sp + 32) + signExtend12 (4008 : BitVec 12)) ↦ₘ u6) **
     (((sp + 32) + signExtend12 (4000 : BitVec 12)) ↦ₘ u7) **
     (((sp + 32) + signExtend12 (3992 : BitVec 12)) ↦ₘ shiftMem) **
     (((sp + 32) + signExtend12 (3984 : BitVec 12)) ↦ₘ nMem) **
     (((sp + 32) + signExtend12 (3976 : BitVec 12)) ↦ₘ jMem) **
     (((sp + 32) + signExtend12 (3968 : BitVec 12)) ↦ₘ retMem) **
     (((sp + 32) + signExtend12 (3960 : BitVec 12)) ↦ₘ dMem) **
     (((sp + 32) + signExtend12 (3952 : BitVec 12)) ↦ₘ dloMem) **
     (((sp + 32) + signExtend12 (3944 : BitVec 12)) ↦ₘ scratch_un0) **
     (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem))
    (by pcFree)
    (evm_addmod_dispatch_prefix_spec_within bt sp x5v x6v x7v x11v
      mo1 mo2 mo3 moNC calleeEntry a b)
  -- the N-zero test as a branch over C, with the dead incoming x6 owned and
  -- the pure fact moved to the front of each target post
  have hnz : cpsBranchWithin 8 (bt + 124)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ addmodOverflowBit a b) **
        (.x0 ↦ᵣ (0 : Word)) **
        (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) ** regOwn .x6)
      ((bt + 124) + 28 + signExtend13 (692 : BitVec 13))
        (⌜n0 ||| n1 ||| n2 ||| n3 = 0⌝ ** addmodNZeroCells sp n0 n1 n2 n3)
      ((bt + 124) + 32)
        (⌜¬(n0 ||| n1 ||| n2 ||| n3 = 0)⌝ ** addmodNZeroCells sp n0 n1 n2 n3) := by
    refine cpsBranchWithin_of_forall_regIs_to_regOwn (fun v6Old => ?_)
    have hraw := evm_addmod_phase2_n_zero_test_spec_within
      (sp + 32) (addmodOverflowBit a b) v6Old n0 n1 n2 n3 (bt + 124) 692
    simp only at hraw
    have hC := cpsBranchWithin_extend_code
      (cr' := addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (hmono := fun ad i h =>
        CodeReq.union_mono_left ad i
          (evm_addmod_total_program_code_n_zero_test_sub ad i h))
      hraw
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun h hq => ?_) (fun h hq => ?_) hC
    · xperm_hyp hp
    · unfold addmodNZeroCells
      xperm_hyp hq
    · unfold addmodNZeroCells
      xperm_hyp hq
  rw [show (bt + 124) + 28 + signExtend13 (692 : BitVec 13) = bt + 844 from by
    rw [show signExtend13 (692 : BitVec 13) = (692 : Word) from by decide]
    bv_omega] at hnz
  rw [show (bt + 124) + 32 = bt + 156 from by bv_omega] at hnz
  -- frame the branch with the post-prefix remainder
  have hnzF := cpsBranchWithin_frameR
    (addmodPostPrefixRest sp x1v x2v x9v x10v a b
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem)
    (addmodPostPrefixRest_pcFree sp x1v x2v x9v x10v a b
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem)
    hnz
  have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hq0 : (sp + 32) + signExtend12 (4088 : BitVec 12) = sp + 24 := by
    rw [show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide]
    bv_omega
  have hq1 : (sp + 32) + signExtend12 (4080 : BitVec 12) = sp + 16 := by
    rw [show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide]
    bv_omega
  have hq2 : (sp + 32) + signExtend12 (4072 : BitVec 12) = sp + 8 := by
    rw [show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide]
    bv_omega
  have hq3 : (sp + 32) + signExtend12 (4064 : BitVec 12) = sp := by
    rw [show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide]
    bv_omega
  refine cpsBranchWithin_weaken (fun h hp => ?pre) (fun _ hq => hq) (fun _ hq => hq)
    (cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr ?mid hpre hnzF)
  case pre =>
    unfold addmodTotalEntry at hp
    xperm_hyp hp
  case mid =>
    intro h hp
    simp only [addmodPostPrefixRest,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold, evmWordIs,
      hq0, hq1, hq2, hq3] at hp ⊢
    xperm_hyp hp

-- ============================================================================
-- The carry arm extended to the join (byte 160 → 864)
-- ============================================================================

/-- The carry branch followed by its exit `JAL x0, 32` (byte 832 → 864):
    extends `evm_addmod_carry_branch_stack_spec_within` to the common join. -/
theorem evm_addmod_carry_branch_to_join_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (a b : EvmWord)
    (hr : EvmWord.fromLimbs ![r0, r1, r2, r3] = a + b)
    (hcarry : (EvmWord.addCarry a b).fst = true)
    (hN : EvmWord.fromLimbs ![n0, n1, n2, n3] ≠ 0)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (hoffset3 : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign3 : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj3 : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      ((((((21 + (1 + (unifiedDivBound + 1))) + 1) + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
          + ((24 + (1 + (unifiedDivBound + 1))) + 1))
        + (((8 + 30) + 25) + 30)) + 1)
      (bt + 160) (bt + 864)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodLdResultOwned F
        (EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3]))) := by
  have hc := evm_addmod_carry_branch_stack_spec_within
    bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem
    mo1 mo2 mo3 moNC calleeEntry a b hr hcarry hN
    hoffset1 callerAlign1 hoffset2 callerAlign2 hoffset3 callerAlign3
    retAlign hdisj1 hdisj2 hdisj3 hdisjTC
  have hjal := jal_x0_spec_gen_within 32 (bt + 832)
  rw [show (bt + 832) + signExtend21 (32 : BitVec 21) = bt + 864 from by
    rw [show signExtend21 (32 : BitVec 21) = (32 : Word) from by decide]
    bv_omega] at hjal
  have hjalC := carry_block_in_C
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun ad i h => evm_addmod_total_program_code_carry_exit_jal_sub ad i (by
      rw [show CodeReq.ofProg (bt + 832) (JAL .x0 32)
          = CodeReq.singleton (bt + 832) (.JAL .x0 32) from CodeReq.ofProg_singleton]
      exact h))
    hjal
  have hjalF := cpsTripleWithin_frameR
    (addmodLdResultOwned F
      (EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3])))
    (by
      unfold addmodLdResultOwned evmWordIs evmWordOwn
      rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold]
      pcFree)
    hjalC
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?post)
    (cpsTripleWithin_seq_perm_same_cr ?mid hc hjalF)
  case mid =>
    intro h hp
    exact (sepConj_emp_left h).mpr hp
  case post =>
    exact (sepConj_emp_left h).mp hq

-- ============================================================================
-- The unconditional total ADDMOD stack spec (byte 0 → 864 over C)
-- ============================================================================

/-- Frame carried through the carry-test `BEQ x7, x0` at byte 156: everything
    except `x7`/`x0`, in the post-N-zero-test state. -/
def addmodBeqFrame (sp : Word)
    (x1v x2v x9v x10v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** (.x6 ↦ᵣ (n0 ||| n1 ||| n2 ||| n3)) ** (.x5 ↦ᵣ n3) **
  (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) **
  (.x11 ↦ᵣ (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3)
            then (1 : Word) else 0)) **
  evmWordIs (sp + 32) (a + b) **
  (((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
  (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
  (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
  (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
  (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
  (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
  (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
  (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
  (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
  divScratchValuesCallNoX1 (sp + 32)
    (a.getLimbN 3) (a.getLimbN 2) (a.getLimbN 1) (a.getLimbN 0)
    u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
  (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)

theorem addmodBeqFrame_pcFree (sp : Word)
    (x1v x2v x9v x10v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) :
    (addmodBeqFrame sp x1v x2v x9v x10v a b n0 n1 n2 n3
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem).pcFree := by
  unfold addmodBeqFrame evmWordIs
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  pcFree

/-- **The unconditional total ADDMOD stack spec** (byte 0 → 864 over `C`):
    from the ADDMOD dispatch entry — `x12 = sp`, operands `a`/`b` and modulus
    limbs `n0..n3` on the EVM stack, generic dispatcher registers, park and
    callable-scratch cells — to `EvmWord.addmod a b N` at `sp+64..88` with
    `x12 = sp+64` (`addmodLdResultOwned`), for EVERY input: the `N = 0`,
    no-carry, and carry-out branches are all covered. The only hypotheses are
    the dispatcher-pinned code-layout side conditions (call-site offsets,
    alignment, and code-region disjointness). -/
theorem evm_addmod_total_stack_spec_within
    (bt sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (hoffset3 : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign3 : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (hoffsetNC : (bt + 836) + signExtend21 moNC = calleeEntry)
    (callerAlignNC : ((bt + 836) + 4) &&& ~~~(1 : Word) = (bt + 836) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj3 : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjNC : (CodeReq.singleton (bt + 836) (.JAL .x1 moNC)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      (((30 + 1) + 8) +
        (1 + ((((((21 + (1 + (unifiedDivBound + 1))) + 1)
            + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
            + ((24 + (1 + (unifiedDivBound + 1))) + 1))
          + (((8 + 30) + 25) + 30)) + 1)))
      bt (bt + 864)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (addmodTotalEntry sp x1v x2v x5v x6v x7v x9v x10v x11v a b
        n0 n1 n2 n3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
        u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
        scratch_un0 scratchMem)
      (addmodLdResultOwned (sp + 32)
        (EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3]))) := by
  have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  have hq0 : (sp + 32) + signExtend12 (4088 : BitVec 12) = sp + 24 := by
    rw [show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide]
    bv_omega
  have hq1 : (sp + 32) + signExtend12 (4080 : BitVec 12) = sp + 16 := by
    rw [show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide]
    bv_omega
  have hq2 : (sp + 32) + signExtend12 (4072 : BitVec 12) = sp + 8 := by
    rw [show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide]
    bv_omega
  have hq3 : (sp + 32) + signExtend12 (4064 : BitVec 12) = sp := by
    rw [show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide]
    bv_omega
  have hr : EvmWord.fromLimbs
      ![(a + b).getLimbN 0, (a + b).getLimbN 1, (a + b).getLimbN 2, (a + b).getLimbN 3]
      = a + b := fromLimbs_getLimbN_vec (a + b)
  have hbr := evm_addmod_dispatch_branch_spec_within
    bt sp x1v x2v x5v x6v x7v x9v x10v x11v a b
    n0 n1 n2 n3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
    u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
    scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry
  by_cases hz : n0 ||| n1 ||| n2 ||| n3 = 0
  · -- ZERO branch: the fall-through arm is refuted by `hz`
    have htaken := cpsBranchWithin_takenPath hbr (fun hp hq => by
      obtain ⟨h1, h2, _, _, hL, _⟩ := hq
      obtain ⟨h3, h4, _, _, hpure, _⟩ := hL
      exact hpure.2 hz)
    obtain ⟨hn0, hn1, hn2, hn3⟩ := or4_eq_zero hz
    have harm := evm_addmod_zero_branch_spec_within
      bt (sp + 32) n3 n0 n1 n2 n3
      ((a + b).getLimbN 0) ((a + b).getLimbN 1) ((a + b).getLimbN 2) ((a + b).getLimbN 3)
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
      x1v x2v (n0 ||| n1 ||| n2 ||| n3)
      (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)) x9v x10v
      (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3) then (1 : Word) else 0)
      sm0 sm1 sm2 sm3
      (a.getLimbN 3) (a.getLimbN 2) (a.getLimbN 1) (a.getLimbN 0)
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry a b hn0 hn1 hn2 hn3
    refine cpsTripleWithin_mono_nSteps ?zle
      (cpsTripleWithin_seq_perm_same_cr ?zmid htaken harm)
    case zle => omega
    intro h hp
    have hp' := sepConj_mono_left
      (fun h' hcp => ((sepConj_pure_left h').mp hcp).2) h hp
    simp only [addmodNZeroCells, addmodPostPrefixRest,
      addmodLaTail, addmodLaRegTail, addmodLaScratchTail, evmWordIs,
      e0, e8, e16, e24, add_zero] at hp' ⊢
    generalize (a + b).getLimbN 0 = g0 at hp' ⊢
    generalize (a + b).getLimbN 1 = g1 at hp' ⊢
    generalize (a + b).getLimbN 2 = g2 at hp' ⊢
    generalize (a + b).getLimbN 3 = g3 at hp' ⊢
    generalize (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)) = gx7 at hp' ⊢
    xperm_hyp hp'
  · -- N ≠ 0: the zero arm is refuted; continue to the carry test
    have h156 := cpsBranchWithin_ntakenPath hbr (fun hp hq => by
      obtain ⟨h1, h2, _, _, hL, _⟩ := hq
      obtain ⟨h3, h4, _, _, hpure, _⟩ := hL
      exact hz hpure.2)
    have h156' := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => sepConj_mono_left
        (fun h' hcp => ((sepConj_pure_left h').mp hcp).2) h hq)
      h156
    have hN4 := fromLimbs_ne_zero_of_or4 hz
    -- the carry-test BEQ at byte 156, framed
    have hbeq_raw := beq_spec_gen_within .x7 .x0 (680 : BitVec 13)
      (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)) (0 : Word) (bt + 156)
    have hbeqC := cpsBranchWithin_extend_code
      (cr' := addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (hmono := fun ad i h =>
        CodeReq.union_mono_left ad i
          (evm_addmod_total_program_code_carry_test_sub ad i (by
            rw [show CodeReq.ofProg (bt + 156) (BEQ .x7 .x0 680)
                = CodeReq.singleton (bt + 156) (.BEQ .x7 .x0 680)
              from CodeReq.ofProg_singleton]
            exact h)))
      hbeq_raw
    have hbeqW := cpsBranchWithin_weaken (fun _ hp => hp)
      (fun h hq => by xperm_hyp hq) (fun h hq => by xperm_hyp hq)
      (Q_t' := ⌜addmodOverflowBit a b + signExtend12 (0 : BitVec 12) = 0⌝ **
        ((.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word))))
      (Q_f' := ⌜¬(addmodOverflowBit a b + signExtend12 (0 : BitVec 12) = 0)⌝ **
        ((.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word))))
      hbeqC
    have hbeqF := cpsBranchWithin_frameR
      (addmodBeqFrame sp x1v x2v x9v x10v a b n0 n1 n2 n3
        sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
        u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
        scratch_un0 scratchMem)
      (addmodBeqFrame_pcFree sp x1v x2v x9v x10v a b n0 n1 n2 n3
        sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
        u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
        scratch_un0 scratchMem)
      hbeqW
    rw [show (bt + 156) + signExtend13 (680 : BitVec 13) = bt + 836 from by
      rw [show signExtend13 (680 : BitVec 13) = (680 : Word) from by decide]
      bv_omega] at hbeqF
    rw [show (bt + 156) + 4 = bt + 160 from by bv_omega] at hbeqF
    have hbeqfull := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by
        simp only [addmodNZeroCells, addmodPostPrefixRest, addmodBeqFrame] at hp ⊢
        xperm_hyp hp)
      h156' hbeqF
    by_cases hc : addmodOverflowBit a b + signExtend12 (0 : BitVec 12) = 0
    · -- NO-CARRY: the fall-through (carry) arm is refuted by `hc`
      have htk := cpsBranchWithin_takenPath hbeqfull (fun hp hq => by
        obtain ⟨h1, h2, _, _, hL, _⟩ := hq
        obtain ⟨h3, h4, _, _, hpure, _⟩ := hL
        exact hpure.2 hc)
      have hnc : (EvmWord.addCarry a b).fst = false := by
        have h0 : addmodOverflowBit a b = 0 := by
          rwa [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, add_zero] at hc
        unfold addmodOverflowBit at h0
        by_cases hge : a.toNat + b.toNat ≥ 2 ^ 256
        · rw [if_pos hge] at h0
          exact absurd h0 (by decide)
        · simp only [EvmWord.addCarry, decide_eq_false_iff_not]
          omega
      have harm := evm_addmod_no_carry_branch_spec_within
        bt (sp + 32) n3 n0 n1 n2 n3
        ((a + b).getLimbN 0) ((a + b).getLimbN 1) ((a + b).getLimbN 2) ((a + b).getLimbN 3)
        sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
        x1v x2v (n0 ||| n1 ||| n2 ||| n3)
        (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)) x9v x10v
        (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3) then (1 : Word) else 0)
        sm0 sm1 sm2 sm3
        (a.getLimbN 3) (a.getLimbN 2) (a.getLimbN 1) (a.getLimbN 0)
        u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
        scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry a b hr hnc
        hoffsetNC callerAlignNC retAlign hdisjNC hdisjTC
      refine cpsTripleWithin_mono_nSteps ?nle
        (cpsTripleWithin_seq_perm_same_cr ?nmid htk harm)
      case nle => omega
      intro h hp
      have hp' := sepConj_mono_left
        (fun h' hcp => ((sepConj_pure_left h').mp hcp).2) h hp
      simp only [addmodBeqFrame, addmodLaTail, addmodLaRegTail, addmodLaScratchTail,
        evmWordIs, e0, e8, e16, e24, add_zero] at hp' ⊢
      generalize (a + b).getLimbN 0 = g0 at hp' ⊢
      generalize (a + b).getLimbN 1 = g1 at hp' ⊢
      generalize (a + b).getLimbN 2 = g2 at hp' ⊢
      generalize (a + b).getLimbN 3 = g3 at hp' ⊢
      generalize (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)) = gx7 at hp' ⊢
      xperm_hyp hp'
    · -- CARRY: the taken (no-carry) arm is refuted by `hc`
      have hnt := cpsBranchWithin_ntakenPath hbeqfull (fun hp hq => by
        obtain ⟨h1, h2, _, _, hL, _⟩ := hq
        obtain ⟨h3, h4, _, _, hpure, _⟩ := hL
        exact hc hpure.2)
      have hcarry : (EvmWord.addCarry a b).fst = true := by
        by_cases hge : a.toNat + b.toNat ≥ 2 ^ 256
        · simp only [EvmWord.addCarry, decide_eq_true_eq]
          omega
        · exfalso
          apply hc
          rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, add_zero]
          unfold addmodOverflowBit
          rw [if_neg hge]
      have harm := evm_addmod_carry_branch_to_join_spec_within
        bt (sp + 32) n3 n0 n1 n2 n3
        ((a + b).getLimbN 0) ((a + b).getLimbN 1) ((a + b).getLimbN 2) ((a + b).getLimbN 3)
        sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
        x1v x2v (n0 ||| n1 ||| n2 ||| n3)
        (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)) x9v x10v
        (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3) then (1 : Word) else 0)
        sm0 sm1 sm2 sm3
        (a.getLimbN 3) (a.getLimbN 2) (a.getLimbN 1) (a.getLimbN 0)
        u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
        scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry a b hr hcarry hN4
        hoffset1 callerAlign1 hoffset2 callerAlign2 hoffset3 callerAlign3
        retAlign hdisj1 hdisj2 hdisj3 hdisjTC
      refine cpsTripleWithin_mono_nSteps ?cle
        (cpsTripleWithin_seq_perm_same_cr ?cmid hnt harm)
      case cle => omega
      intro h hp
      have hp' := sepConj_mono_left
        (fun h' hcp => ((sepConj_pure_left h').mp hcp).2) h hp
      simp only [addmodBeqFrame, addmodLaTail, addmodLaRegTail, addmodLaScratchTail,
        evmWordIs, e0, e8, e16, e24, add_zero] at hp' ⊢
      generalize (a + b).getLimbN 0 = g0 at hp' ⊢
      generalize (a + b).getLimbN 1 = g1 at hp' ⊢
      generalize (a + b).getLimbN 2 = g2 at hp' ⊢
      generalize (a + b).getLimbN 3 = g3 at hp' ⊢
      generalize (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)) = gx7 at hp' ⊢
      xperm_hyp hp'

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Owned frame of the clean ADDMOD result post: every register and scratch
    cell the opcode clobbers, shed to ownership, at the post-prologue frame
    base `F = sp + 32`. This is `addmodLdResultOwned` minus its leading
    `x12`/result-word atoms (which the public post states explicitly). -/
def addmodResultOwnedFrame (F : Word) : Assertion :=
  regOwn .x0 ** regOwn .x1 ** regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x9 ** regOwn .x10 ** regOwn .x11 **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  evmWordOwn F **
  memOwn (F + signExtend12 (3872 : BitVec 12)) ** memOwn (F + signExtend12 (3880 : BitVec 12)) **
  memOwn (F + signExtend12 (3888 : BitVec 12)) ** memOwn (F + signExtend12 (3896 : BitVec 12)) **
  memOwn (F + signExtend12 (3840 : BitVec 12)) ** memOwn (F + signExtend12 (3848 : BitVec 12)) **
  memOwn (F + signExtend12 (3856 : BitVec 12)) ** memOwn (F + signExtend12 (3864 : BitVec 12)) **
  memOwn (F + signExtend12 (3904 : BitVec 12)) ** memOwn (F + signExtend12 (3912 : BitVec 12)) **
  memOwn (F + signExtend12 (3920 : BitVec 12)) ** memOwn (F + signExtend12 (3928 : BitVec 12))

/-- **The public total ADDMOD result-stack spec** (byte 0 → 864 over the total
    program ∪ v5 MOD callable): from `evmStackIs sp [a, b, N]` — the three
    operands on the EVM stack — plus the dispatcher register frame and the
    park/callable-scratch cells, to `evmStackIs (sp + 64) [EvmWord.addmod a b N]`
    with `x12 = sp + 64` (popped 3, pushed 1) and the clobbered state shed to
    `addmodResultOwnedFrame`. Unconditional in `a`, `b`, `N` — the `N = 0`,
    no-carry, and carry-out branches are all covered; the only hypotheses are
    the dispatcher-pinned code-layout side conditions. -/
theorem evm_addmod_total_result_stack_spec_within
    (bt sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b N : EvmWord)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (hoffset3 : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign3 : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (hoffsetNC : (bt + 836) + signExtend21 moNC = calleeEntry)
    (callerAlignNC : ((bt + 836) + 4) &&& ~~~(1 : Word) = (bt + 836) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj3 : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjNC : (CodeReq.singleton (bt + 836) (.JAL .x1 moNC)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      (((30 + 1) + 8) +
        (1 + ((((((21 + (1 + (unifiedDivBound + 1))) + 1)
            + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
            + ((24 + (1 + (unifiedDivBound + 1))) + 1))
          + (((8 + 30) + 25) + 30)) + 1)))
      bt (bt + 864)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) **
         (.x5 ↦ᵣ x5v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) ** (.x9 ↦ᵣ x9v) **
         (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v)) **
        evmStackIs sp [a, b, N]) **
       ((((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
        (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
        (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
        (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
        (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
        (((sp + 32) + signExtend12 (4056 : BitVec 12)) ↦ₘ u0) **
        (((sp + 32) + signExtend12 (4048 : BitVec 12)) ↦ₘ u1) **
        (((sp + 32) + signExtend12 (4040 : BitVec 12)) ↦ₘ u2) **
        (((sp + 32) + signExtend12 (4032 : BitVec 12)) ↦ₘ u3) **
        (((sp + 32) + signExtend12 (4024 : BitVec 12)) ↦ₘ u4) **
        (((sp + 32) + signExtend12 (4016 : BitVec 12)) ↦ₘ u5) **
        (((sp + 32) + signExtend12 (4008 : BitVec 12)) ↦ₘ u6) **
        (((sp + 32) + signExtend12 (4000 : BitVec 12)) ↦ₘ u7) **
        (((sp + 32) + signExtend12 (3992 : BitVec 12)) ↦ₘ shiftMem) **
        (((sp + 32) + signExtend12 (3984 : BitVec 12)) ↦ₘ nMem) **
        (((sp + 32) + signExtend12 (3976 : BitVec 12)) ↦ₘ jMem) **
        (((sp + 32) + signExtend12 (3968 : BitVec 12)) ↦ₘ retMem) **
        (((sp + 32) + signExtend12 (3960 : BitVec 12)) ↦ₘ dMem) **
        (((sp + 32) + signExtend12 (3952 : BitVec 12)) ↦ₘ dloMem) **
        (((sp + 32) + signExtend12 (3944 : BitVec 12)) ↦ₘ scratch_un0) **
        (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)))
      (((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
       addmodResultOwnedFrame (sp + 32)) := by
  have h := evm_addmod_total_stack_spec_within bt sp
    x1v x2v x5v x6v x7v x9v x10v x11v a b
    (N.getLimbN 0) (N.getLimbN 1) (N.getLimbN 2) (N.getLimbN 3)
    sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
    u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
    scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry
    hoffset1 callerAlign1 hoffset2 callerAlign2 hoffset3 callerAlign3
    hoffsetNC callerAlignNC retAlign hdisj1 hdisj2 hdisj3 hdisjNC hdisjTC
  rw [fromLimbs_getLimbN_vec] at h
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h
  · -- PRE: the public `evmStackIs sp [a, b, N]` form → `addmodTotalEntry`
    rw [evmStackIs_triple] at hp
    simp only [addmodTotalEntry, evmWordIs,
      signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
      BitVec.add_assoc, BitVec.reduceAdd] at hp ⊢
    xperm_hyp hp
  · -- POST: `addmodLdResultOwned` → the clean `evmStackIs` result form
    simp only [addmodLdResultOwned] at hq
    rw [show ((sp + 32) + 32 : Word) = sp + 64 from by bv_omega] at hq
    rw [evmStackIs_single]
    simp only [addmodResultOwnedFrame]
    xperm_hyp hq

end EvmAsm.Evm64.AddMod.Compose
