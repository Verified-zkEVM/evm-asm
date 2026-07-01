/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedBorrowCarry

  Borrow-dispatched unified n=3 v5 loop: takes `loopN3SelectedBorrowCarryV5` (the
  satisfiable-from-shape carry bundle, #7526) instead of the unsatisfiable
  unconditional `loopN3SelectedCarryV5`, and dispatches the 4 `bltu²` cases to the
  per-case unified-post `_borrowCarry` wrappers (#7536), extracting the two
  per-digit borrow-conditional carries from the bundle in each arm.

  The bundle's j=0 window is `iterN3V5 bltu_1 …` (`@[irreducible]`); the dispatch
  rewrites it with `iterN3V5_true_eq` (→ `iterWithDoubleAddback (divKTrialCallV5QHat …)`)
  and the NAMED `iterN3V5_false_eq_max` (→ `iterN3Max`, *not* the over-unfolded
  `iterWithDoubleAddback (signExtend12 4095)`).  Matching the wrappers' named
  `iterN3Max` window keeps the isDefEq syntactic — the over-unfold to the saturated
  `iterWithDoubleAddback` is exactly what forced the explosive defeq through the
  irreducible `iterN3Max` in earlier attempts.  n3 mirror of
  `divK_loop_n2_unified_from_source_..._borrowCarry`.  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopDefsBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedBorrowCarryCasesMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Borrow-dispatched n=3 v5 unified loop: the carries come from the
    satisfiable-from-shape `loopN3SelectedBorrowCarryV5` bundle (borrow-conditional
    per digit), dispatched to the per-case unified-post `_borrowCarry` wrappers. -/
theorem divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry : loopN3SelectedBorrowCarryV5 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · -- max × max
    have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 :
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        ¬BitVec.ult r1.2.2.2.1 v2 := by
      simp only at hbltu_0 ⊢; rw [← hbltu_0]; decide
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_false_eq_max] at hcarry
    rw [if_neg (by decide), if_neg (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_maxmax_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem hb1 hc1 hb0 hc0
  · -- max × call
    have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 :
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        BitVec.ult r1.2.2.2.1 v2 := by
      simp only at hbltu_0 ⊢; exact hbltu_0.symm
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_false_eq_max] at hcarry
    rw [if_neg (by decide), if_pos (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_maxcall_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0
  · -- call × max
    have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
        ¬BitVec.ult r1.2.2.2.1 v2 := by
      simp only at hbltu_0 ⊢; rw [← hbltu_0]; decide
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_true_eq] at hcarry
    rw [if_pos (by decide), if_neg (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_callmax_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0
  · -- call × call
    have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; exact hbltu_0.symm
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_true_eq] at hcarry
    rw [if_pos (by decide), if_pos (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_callcall_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0

end EvmAsm.Evm64
