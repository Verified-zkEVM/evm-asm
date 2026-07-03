/-
  EvmAsm.Evm64.AddMod.Compose.ZeroNoCarryArms

  Phase-3 M4 for total ADDMOD (issue #9704): the two short branch arms.

  * Zero arm (byte 844 → 864): `phase2_zero_path ;; epilogue` — when `N = 0`
    the zero path stores 0 into the result cells and the epilogue advances
    the stack pointer; the result is `EvmWord.addmod a b 0 = 0`.
  * No-carry arm (byte 836 → 864): a single MOD near-call reduces the exact
    (non-overflowing) truncated sum, then the exit JAL jumps to the join;
    `EvmWord.mod (a+b) N = EvmWord.addmod a b N` via
    `mod_truncated_sum_eq_addmod_of_no_overflow`.

  Both arms take the carry branch's entry frame shape and land the common
  `addmodLdResultOwned F (EvmWord.addmod a b N)` post, so the M5 three-way
  dispatch merges the arms directly.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryLdChain

namespace EvmAsm.Evm64.AddMod.Compose

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

end EvmAsm.Evm64.AddMod.Compose
