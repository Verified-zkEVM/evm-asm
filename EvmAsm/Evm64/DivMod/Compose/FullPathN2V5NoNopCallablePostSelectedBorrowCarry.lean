/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallablePostSelectedBorrowCarry

  Borrow-dispatched n=2 v5 entry→nopOff full path: mirror of #7420
  (`evm_div_n2_stack_pre_to_unified_post_v5_noNop_selectedCarry`) using the
  borrow-dispatched full path (#7451) and taking `loopN2SelectedBorrowCarryV5`
  (satisfiable from shape).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallablePost
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFullBorrowCarry

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem evm_div_n2_stack_pre_to_unified_post_v5_noNop_borrowCarry (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal x9In x2In : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 =
      BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false =>
        BitVec.ult (iterN2Max
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1)
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1)
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | true, false =>
        BitVec.ult (iterN2Max
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
                (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                  (b.getLimbN 2) (b.getLimbN 3)).2.1)
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
                (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                  (b.getLimbN 2) (b.getLimbN 3)).2.1)
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1)
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hcarry : loopN2SelectedBorrowCarryV5 bltu_2 bltu_1 bltu_0
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 1)).2.2.1
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 1)).2.2.2.1
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 1)).2.2.2.2
      (0 : Word) (0 : Word)
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 1)).2.1
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 1)).1) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 702) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (x9In) raVal
        x2In
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hA0 := fullDivN2_preloop_loop_unified_exact_x1_scratch_v5_noNop_borrowCarry
    bltu_2 bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In
    hbnz' hb3z hb2z hb1nz hshift_nz halign hbltu_2
    (by cases bltu_2 <;> simpa using hbltu_1)
    (by cases bltu_2 <;> cases bltu_1 <;> simpa using hbltu_0) hcarry
  have hA : cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 702)
      base (base + denormOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (x9In) raVal
        x2In
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      ((loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.2.1
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.2.2.1
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.2.2.2
        (0 : Word) (0 : Word)
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.1
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 1)).1))) := by
    refine cpsTripleWithin_weaken ?_ (fun _ hq => hq) hA0
    intro _ hp
    rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
    rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
        evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
        divScratchValues_unfold] at hp
    rw [word_add_zero]
    xperm_hyp hp
  have hshift_nz' : fullDivN2Shift (b.getLimbN 1) ≠ 0 := by
    delta fullDivN2Shift
    exact hshift_nz
  have hBNoNop := evm_div_n2_denorm_epilogue_bundled_spec_noNop_v5Final_exact_x1_frame
    bltu_2 bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal hshift_nz'
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FFF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FFT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FTF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FTT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TFF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TFT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TTF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TTT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp)
    hA hBNoNop
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => hq)
    hFull


end EvmAsm.Evm64
