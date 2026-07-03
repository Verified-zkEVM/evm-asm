/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFull

  n=2 v5/no-NOP path from dispatch entry through the loop (entry → denormOff),
  composing the framed preloop (#7414), the v4 loopSetupPost→pre bridge (reused
  verbatim — the v5 loop's pre is the code-agnostic loopN2PreWithScratchV4NoX1),
  and the instantiated selected-carry v5 loop (#7415). Mirror of
  `fullDivN2_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry`
  (FullPathN2V4NoNopPreloop:662) with the v5 trial accessors + 702-step loop.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopPreloop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopSelected
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopLoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem fullDivN2_preloop_loop_unified_exact_x1_scratch_v5_noNop_selectedCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 =
      BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
        (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false =>
        BitVec.ult (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | true, false =>
        BitVec.ult (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
                (fullDivN2NormV b0 b1 b2 b3).2.1)
              (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
                (fullDivN2NormV b0 b1 b2 b3).2.1)
              (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hcarry : loopN2SelectedCarryV5 bltu_2 bltu_1 bltu_0
      (fullDivN2NormV b0 b1 b2 b3).1
      (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.2
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
      (0 : Word) (0 : Word)
      (fullDivN2NormU a0 a1 a2 a3 b1).2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).1) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 702) base (base + denormOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        (fullDivN2NormV b0 b1 b2 b3).1
        (fullDivN2NormV b0 b1 b2 b3).2.1
        (fullDivN2NormV b0 b1 b2 b3).2.2.1
        (fullDivN2NormV b0 b1 b2 b3).2.2.2
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
        (0 : Word) (0 : Word)
        (fullDivN2NormU a0 a1 a2 a3 b1).2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) := by
  have hPre := evm_div_n2_to_loopSetup_spec_within_v5_noNop_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In
    hbnz hb3z hb2z hb1nz hshift_nz
  have hLoop := evm_div_n2_loop_unified_inst_noNop_exact_x1_v5_selectedCarry
    bltu_2 bltu_1 bltu_0 sp base
    (fullDivN2Shift b1) (fullDivN2AntiShift b1)
    (fullDivN2NormV b0 b1 b2 b3).1
    (fullDivN2NormV b0 b1 b2 b3).2.1
    (fullDivN2NormV b0 b1 b2 b3).2.2.1
    (fullDivN2NormV b0 b1 b2 b3).2.2.2
    (fullDivN2NormU a0 a1 a2 a3 b1).1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
    (a0 >>> ((fullDivN2AntiShift b1).toNat % 64)) v11Old jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hbltu_2 (by cases bltu_2 <;> simpa using hbltu_1)
    (by cases bltu_2 <;> cases bltu_1 <;> simpa using hbltu_0) hcarry
  have hLoopf := cpsTripleWithin_frameR
    ((((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1)))
    (by pcFree) hLoop
  have hBridge := loopSetupPost_to_loopN2PreWithScratchV4NoX1_framed
    sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
  have hPre' := cpsTripleWithin_weaken
    (fun h hp => hp)
    hBridge
    hPre
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

end EvmAsm.Evm64
