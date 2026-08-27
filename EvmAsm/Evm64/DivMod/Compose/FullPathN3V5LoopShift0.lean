/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LoopShift0

  v5 n=3 shift=0 LOOP body (loopBodyOff → denormOff) over `divCode_noNop_v5`, with
  the carry hypothesis DISCHARGED FROM SHAPE.  The unified loop
  (`divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry`,
  #7538) is GENERIC in the divisor/window values, so the shift=0 loop is that loop
  instantiated with the RAW divisor `(b0, b1, b2, 0)` (`b2 ≥ 2^63`) and the shift=0
  verbatim-dividend window `u0=a1, u1=a2, u2=a3, u3=0, uTop=0, u0Orig=a0` (read off
  the shift=0 preloop, FullPathN3V5PreloopShift0).  The carry is discharged via
  `loopN3SelectedBorrowCarryV5_shift0_of_shape` (#7553); the `hbltu_0` match form
  is bridged to the clean `iterN3V5` form via `iterN3V5_false_eq_max` /
  `iterN3V5_true_eq`.  n=3 analog of `divK_loop_n2_shift0_param_v5_noNop`.
  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedBorrowCarry
public import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0BundleOfShape

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Flag-parameterized shift=0 LOOP body (`loopBodyOff → denormOff`): the unified
    n=3 loop (#7538) instantiated with the raw divisor + verbatim-dividend window,
    the carry discharged from shape. -/
theorem divK_loop_n3_shift0_param_v5_noNop (bltu_1 bltu_0 : Bool)
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hb2ge : b2.toNat ≥ 2 ^ 63)
    (hbltu_1 : bltu_1 = BitVec.ult (0 : Word) b2)
    (hbltu_0 : bltu_0 =
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        b0 b1 b2 0 a1 a2 a3 0 0 a0 q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        b0 b1 b2 0 a1 a2 a3 0 0 a0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  apply divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    bltu_1 bltu_0 sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    b0 b1 b2 0 a1 a2 a3 0 0 a0 q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign
  case hbltu_1 =>
    exact hbltu_1
  case hbltu_0 =>
    cases bltu_1 <;>
      simp only [iterN3V5_false_eq_max, iterN3V5_true_eq] at hbltu_0 ⊢ <;> exact hbltu_0
  case hcarry =>
    exact loopN3SelectedBorrowCarryV5_shift0_of_shape a0 a1 a2 a3 b0 b1 b2
      bltu_1 bltu_0 hb2ge
      (fun h => by rw [← hbltu_1]; exact h)
      (fun h => by rw [← hbltu_1, h]; decide)
      (fun h => by rw [← hbltu_0]; exact h)
      (fun h => by rw [← hbltu_0, h]; decide)

end EvmAsm.Evm64
