/-
# `extract_pure` — slice 2 of #1432 (beads evm-asm-455)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This file implements the `extract_pure` tactic designed in slice 1
(beads evm-asm-bx7). Slice 3 (beads evm-asm-8f5) will rewrite the call
sites listed in the slice-1 design notes to use this tactic.

## Overview

`extract_pure h` rewrites a hypothesis `h : (… ** ⌜P⌝ ** … ** ⌜Q⌝ ** …) s`
into a chain of `∧` applications by AC-normalising the `sepConj` chain and
applying `sepConj_pure_left` / `sepConj_pure_right` to bubble pure atoms
out. After the rewrite, the user can `obtain` directly without manually
walking the chain.

The implementation is a one-liner `simp only [...]` macro: it relies on
the AC equalities `sepConj_assoc'`, `sepConj_comm'`, `sepConj_left_comm'`
already used by `sep_perm`, plus the two pure-extraction biconditionals
`sepConj_pure_left` and `sepConj_pure_right` (proved in `SepLogic.lean`),
plus the `empAssertion` collapse rules.

We deliberately keep the surface small: callers say `extract_pure h`,
then use plain `obtain ⟨hP, hQ, …, hRest⟩ := h` to name the extracted
purities. The richer `with ⟨…⟩` / `using P` forms sketched in slice 1
are not needed in practice — `obtain` already provides them.
-/

import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Rv64.Tactics

open EvmAsm.Rv64

-- Helper iff lemmas that bubble `⌜·⌝` atoms outward through one layer of
-- associativity. Together with `sepConj_pure_left` / `sepConj_pure_right`
-- they let `simp only` drain every pure atom out of a right-associated
-- `**`-chain, regardless of where in the chain it sits.

theorem sepConj_pure_mid_left {P : Assertion} {Q : Prop} {R : Assertion} :
    ∀ s, (P ** ⌜Q⌝ ** R) s ↔ Q ∧ (P ** R) s := by
  intro s
  rw [show (P ** ⌜Q⌝ ** R) = (⌜Q⌝ ** P ** R) from by
        rw [← sepConj_assoc', ← sepConj_assoc', sepConj_comm' P (⌜Q⌝)]]
  exact sepConj_pure_left s

theorem sepConj_pure_mid_right {P R : Assertion} {Q : Prop} :
    ∀ s, (P ** R ** ⌜Q⌝) s ↔ Q ∧ (P ** R) s := by
  intro s
  rw [show (P ** R ** ⌜Q⌝) = (⌜Q⌝ ** P ** R) from by
        rw [sepConj_comm' R (⌜Q⌝), ← sepConj_assoc',
            sepConj_comm' P (⌜Q⌝), sepConj_assoc']]
  exact sepConj_pure_left s

/-- `extract_pure h` rewrites a separation-logic hypothesis
    `h : (A₁ ** … ** Aₙ) s` into a `∧`-chain whose left conjuncts are
    the pure atoms (`⌜P⌝`) extracted from the chain and whose tail is
    the remaining resource assertion applied to `s`.

    After `extract_pure h`, follow up with `obtain ⟨hP₁, …, hPₖ, hRest⟩ := h`
    to name the extracted purities and the resource tail.

    Example:
    ```
    example (s : PartialState) (R : Assertion) (P Q : Prop)
        (h : (R ** ⌜P⌝ ** ⌜Q⌝) s) : P ∧ Q := by
      extract_pure h
      exact ⟨h.1, h.2.1⟩
    ```
    -/
macro "extract_pure" h:ident : tactic =>
  `(tactic|
      simp only
        [ EvmAsm.Rv64.sepConj_assoc'
        , EvmAsm.Rv64.sepConj_pure_left
        , EvmAsm.Rv64.sepConj_pure_right
        , EvmAsm.Rv64.Tactics.sepConj_pure_mid_left
        , EvmAsm.Rv64.Tactics.sepConj_pure_mid_right
        , EvmAsm.Rv64.sepConj_emp_left'
        , EvmAsm.Rv64.sepConj_emp_right'
        ] at $h:ident)

end EvmAsm.Rv64.Tactics

/- ============================================================================
   Smoke tests
   ============================================================================
   These exercise the tactic on shapes representative of the slice-3 sites
   without depending on any RISC-V program/spec infrastructure: a single
   pure atom, multiple pure atoms, and pure atoms buried under several
   layers of `**`.
-/

namespace EvmAsm.Rv64.Tactics.ExtractPureTests

open EvmAsm.Rv64

/-- Single pure on the right of a resource. -/
example (s : PartialState) (P : Prop) (R : Assertion)
    (h : (R ** ⌜P⌝) s) : P := by
  extract_pure h
  exact h.2

/-- Single pure on the left of a resource. -/
example (s : PartialState) (P : Prop) (R : Assertion)
    (h : (⌜P⌝ ** R) s) : P := by
  extract_pure h
  exact h.1

/-- Two pure atoms surrounding a resource. -/
example (s : PartialState) (P Q : Prop) (R : Assertion)
    (h : (⌜P⌝ ** R ** ⌜Q⌝) s) : P ∧ Q := by
  extract_pure h
  exact ⟨h.2.1, h.1⟩

/-- Pure atom in the middle of a chain — slice-3 representative shape. -/
example (s : PartialState) (P : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** ⌜P⌝ ** R₂) s) : P := by
  extract_pure h
  exact h.1

/-- Three pure atoms across associativity layers. -/
example (s : PartialState) (P Q R : Prop) (A : Assertion)
    (h : ((⌜P⌝ ** A) ** (⌜Q⌝ ** ⌜R⌝)) s) : P ∧ Q ∧ R := by
  extract_pure h
  refine ⟨?_, ?_, ?_⟩ <;> simp_all

end EvmAsm.Rv64.Tactics.ExtractPureTests
