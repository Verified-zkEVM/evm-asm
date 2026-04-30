/-
  EvmAsm.Evm64.DivMod.Shift0Dispatcher

  Top-level n=4 shift=0 stack spec: unifies the call+skip and call+addback-BEQ
  sub-paths via runtime dispatch on `isSkipBorrowN4Shift0Evm`. Under shift=0,
  the first-addback carry is always 1 (proved in Shift0AddbackMod), so the
  `isAddbackCarry2NzN4Shift0Evm` hypothesis required by the addback-BEQ spec
  is vacuously true and doesn't need to be supplied at this level.
-/

-- `Shift0AddbackMod` transitively imports `SpecCall`.
import EvmAsm.Evm64.DivMod.Shift0AddbackMod
import EvmAsm.Evm64.DivMod.SpecCallShift0

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- Under shift=0, `isAddbackCarry2NzN4Shift0Evm` is vacuously true whenever
    `isAddbackBorrowN4Shift0Evm` holds — the first-addback carry is always 1
    (proved in `n4_shift0_addback_carry_nz`), so the implication's premise
    `first-addback-carry = 0` is false. -/
theorem n4_shift0_addback_carry2_nz_of_borrow (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    isAddbackCarry2NzN4Shift0Evm a b := by
  rw [isAddbackCarry2NzN4Shift0Evm_def]
  unfold isAddbackCarry2NzN4Shift0 isAddbackCarry2NzN4Call isAddbackCarry2Nz
  simp only []
  have h_carry_nz := n4_shift0_addback_carry_nz a b hbnz hshift_z hborrow
  simp only [] at h_carry_nz
  intro h_carry_zero
  exact absurd h_carry_zero h_carry_nz

/-- **n=4 shift=0 DIV top-level dispatcher.**

    Covers the full n=4 shift=0 control-flow tree: `isSkipBorrowN4Shift0Evm`
    goes via call+skip, otherwise via call+addback-BEQ. Both paths produce
    the same `divN4CallSkipStackPost` shape.

    Note: this combinator only needs the skip-or-addback disjunction — the
    addback-BEQ `carry2_nz` precondition is derived automatically via
    `n4_shift0_addback_carry2_nz_of_borrow` (vacuity under shift=0). -/
theorem evm_div_n4_shift0_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12)
      base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  by_cases h_skip : isSkipBorrowN4Shift0Evm a b
  · exact cpsTripleWithin_mono_nSteps (by decide) <|
      evm_div_n4_shift0_call_skip_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z halign h_skip
  · -- ¬ isSkipBorrowN4Shift0Evm → isAddbackBorrowN4Shift0Evm (complementary).
    have h_addback : isAddbackBorrowN4Shift0Evm a b := by
      rw [isAddbackBorrowN4Shift0Evm_def]
      rw [isSkipBorrowN4Shift0Evm_def] at h_skip
      unfold isSkipBorrowN4Shift0 at h_skip
      unfold isAddbackBorrowN4Shift0
      simp only [] at h_skip ⊢
      exact h_skip
    have h_carry2_nz := n4_shift0_addback_carry2_nz_of_borrow a b hbnz hshift_z h_addback
    exact evm_div_n4_shift0_call_addback_beq_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z halign h_carry2_nz h_addback

/-- **n=4 shift=0 MOD top-level dispatcher.** Mirror of the DIV dispatcher. -/
theorem evm_mod_n4_shift0_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12)
      base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  by_cases h_skip : isSkipBorrowN4Shift0Evm a b
  · exact cpsTripleWithin_mono_nSteps (by decide) <|
      evm_mod_n4_shift0_call_skip_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z halign h_skip
  · have h_addback : isAddbackBorrowN4Shift0Evm a b := by
      rw [isAddbackBorrowN4Shift0Evm_def]
      rw [isSkipBorrowN4Shift0Evm_def] at h_skip
      unfold isSkipBorrowN4Shift0 at h_skip
      unfold isAddbackBorrowN4Shift0
      simp only [] at h_skip ⊢
      exact h_skip
    have h_carry2_nz := n4_shift0_addback_carry2_nz_of_borrow a b hbnz hshift_z h_addback
    exact evm_mod_n4_shift0_call_addback_beq_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z halign h_carry2_nz h_addback

end EvmAsm.Evm64
