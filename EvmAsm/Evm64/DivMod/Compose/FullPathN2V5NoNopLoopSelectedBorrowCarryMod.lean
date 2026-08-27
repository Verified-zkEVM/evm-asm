/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopSelectedBorrowCarryMod

  MOD mirror of `FullPathN2V5NoNopLoopSelectedBorrowCarry`: instantiated
  borrow-dispatched n=2 v5 loop over `modCode_noNop_v5` (register-slot form,
  cp + surgical swaps).  Re-exposes the MOD borrow-dispatched unified loop
  (brick 25) with loop-setup register slots named, taking
  `loopN2SelectedBorrowCarryV5` (satisfiable from shape).  Post code-agnostic.
  Brick 26 of the n=2 MOD loop body.  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnifiedBorrowCarryMod

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem evm_mod_n2_loop_unified_inst_noNop_exact_x1_v5_borrowCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift v0' v1' v2' v3' u0S u1S u2S u3S u4_s : Word)
    (v10_val v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u4_s v1')
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false => BitVec.ult (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1'
      | true =>
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
          v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1')
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1')
    (hcarry : loopN2SelectedBorrowCarryV5 bltu_2 bltu_1 bltu_0
      v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S) :
    cpsTripleWithin 702 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jMem (2 : Word) shift u0S v10_val v11Old antiShift
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
        u1S u0S (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;>
  (simp only at hbltu_0 hbltu_1 hbltu_2;
   exact divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
     _ _ _ sp base
     jMem (2 : Word) shift u0S v10_val v11Old antiShift
     v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
     (0 : Word) (0 : Word) (0 : Word) raVal
     retMem dMem dloMem scratch_un0 scratchMem
     halign hbltu_2 hbltu_1 hbltu_0 hcarry)

end EvmAsm.Evm64
