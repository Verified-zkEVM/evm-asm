/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopSelectedBorrowCarry

  Borrow-conditional instantiation of the v5 no-NOP exact-`x1` n=3 loop with
  explicit normalized values: the `_borrowCarry` analog of
  `evm_div_n3_loop_unified_inst_noNop_exact_x1_v5_selectedCarry` (#7521).  Plugs
  the preloop's normalized divisor/window (`shift`/`antiShift`/`b0'..b3'`/`u1..u4`,
  `j = 3`, `uTop = 0`) into the borrow-dispatched loop (#7538), taking the
  satisfiable-from-shape `loopN3SelectedBorrowCarryV5` bundle in place of the
  unconditional selected carries.  The bundle is discharged from shape later by the
  from-shape composition.  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedBorrowCarryMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Borrow-conditional instantiation of the v5 no-NOP exact-`x1` n=3 loop with
    explicit normalized values (the form the preloop composition consumes), feeding
    the `loopN3SelectedBorrowCarryV5` bundle. -/
theorem evm_mod_n3_loop_unified_inst_noNop_exact_x1_v5_borrowCarry_modCode
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2'
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u4 u3 b2')
            b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry : loopN3SelectedBorrowCarryV5 bltu_1 bltu_0
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
    bltu_1 bltu_0 sp base jMem (3 : Word) shift u0 v10Old v11Old antiShift
    b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_1 hbltu_0 hcarry

end EvmAsm.Evm64
