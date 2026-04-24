/-
  EvmAsm.Evm64.Multiply.Spec

  Stack-level 256-bit EVM MUL spec: composes `evm_mul_spec` (column-organized
  schoolbook multiply) with `mul_correct` (the bridge lemma proving that each
  output limb equals the corresponding limb of `a * b`).

  Follows the DivMod stack-spec pattern — the postcondition is bundled in an
  `@[irreducible] def` so `xperm_hyp` only sees a few opaque top-level atoms
  (see AGENTS.md §"XPerm Scaling Limits and Sub-Assertion Bundling"). Scratch
  registers and clobbered stack cells are weakened to `regOwn`/`memOwn`, so
  the column intermediates from the schoolbook algorithm do not leak into
  the consumer-facing contract.
-/

-- `Multiply.LimbSpec → Multiply.Program → Stack`.
import EvmAsm.Evm64.Multiply.LimbSpec
import EvmAsm.Evm64.EvmWordArith.MulCorrect

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Stack-level postcondition
-- ============================================================================

/-- Stack-level MUL postcondition.

    After 63 MUL instructions + 1 ADDI epilogue:
    * `x12 ↦ᵣ sp + 32` — EVM stack pointer advances by 32 (`a` popped, result
      overwrites `b`).
    * `regOwn` for each scratch register (`x5, x6, x7, x10, x11`): caller
      regains ownership but the values are unspecified.
    * `memOwn` for each cell below the new sp (`sp, sp+8, sp+16, sp+24`).
      The first two still carry the unchanged `a[0], a[1]`; the last two
      were spilled with column `r3` partials. All four are below the new
      stack pointer, so callers don't care about their contents.
    * `evmWordIs (sp + 32) (a * b)` — the 256-bit product on the new stack top.

    Bundled as `@[irreducible]` so consumers see a few opaque atoms rather
    than an 11-atom flat conjunction. -/
@[irreducible]
def evmMulStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** memOwn (sp + 24) **
  evmWordIs (sp + 32) (a * b)

-- ============================================================================
-- Weakening lemma
-- ============================================================================

/-- Bridge: concrete register/memory atoms at scratch positions imply
    `evmMulStackPost`. The `x12`-register and `evmWordIs (sp+32)` atoms pass
    through unchanged; the five `regIs` become `regOwn` and the four
    below-sp `memIs` become `memOwn`.

    Proved once, invoked from `evm_mul_stack_spec`'s consequence callback. -/
private theorem mul_stack_weaken (sp : Word) (a b : EvmWord)
    {v5 v6 v7 v10 v11 sp_v sp8_v sp16_v sp24_v : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ sp_v) ** ((sp + 8) ↦ₘ sp8_v) **
       ((sp + 16) ↦ₘ sp16_v) ** ((sp + 24) ↦ₘ sp24_v) **
       evmWordIs (sp + 32) (a * b)) h →
      evmMulStackPost sp a b h := by
  intro h hp
  delta evmMulStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 5 apply sepConj_mono (regIs_implies_regOwn _)
  iterate 3 apply sepConj_mono (memIs_implies_memOwn)
  exact sepConj_mono_left (memIs_implies_memOwn)

-- ============================================================================
-- Stack-level MUL spec
-- ============================================================================

/-- Stack-level 256-bit EVM MUL.
    Pops two EvmWords at `sp` and `sp+32`, writes `a * b` to `sp+32`, advances
    sp by 32. 63 MUL instructions + 1 ADDI epilogue = 252 bytes.

    The postcondition is `evmMulStackPost sp a b` — see its doc comment for
    the register/memory layout on exit. -/
theorem evm_mul_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word) :
    cpsTriple base (base + 252) (evm_mul_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (evmMulStackPost sp a b) := by
  -- Raw column-organized limb-level spec with explicit limbs of a, b
  have h_main := evm_mul_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11
  -- Correctness bridge: each output column equals a limb of (a * b).
  -- mul_correct returns `getLimb` (Fin 4) equalities; rewrite to `getLimbN`
  -- (Nat) form so the atoms match `evmWordIs_sp32_limbs_eq`'s expected shape.
  have ⟨h0, h1, h2, h3⟩ := EvmWord.mul_correct a b
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
             EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
    at h0 h1 h2 h3
  exact cpsTriple_weaken
    (fun h hp => by
      -- Pre: unfold `evmWordIs sp a` and `evmWordIs (sp+32) b` into 4 raw
      -- memIs atoms each, then permute to match the raw evm_mul_spec pre.
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl] at hp
      xperm_hyp hp)
    (fun h hq => by
      -- Post: the raw spec leaves the last 4 memory atoms holding the column
      -- results (c0_r0, c1_r1, c2_r2, r3_final). Fold them into
      -- `evmWordIs (sp+32) (a*b)` via the mul_correct bridge equalities,
      -- then weaken the 5 scratch registers + 4 below-sp cells to *Own.
      rw [← evmWordIs_sp32_limbs_eq sp (a * b) _ _ _ _ h0 h1 h2 h3] at hq
      exact mul_stack_weaken sp a b h (by xperm_hyp hq))
    h_main

end EvmAsm.Evm64
