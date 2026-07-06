/-
# `extract_pure` / `extract_pure_deep` — slice 2 of #1432

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This file implements the pure-extraction tactics designed in slice 1
(beads evm-asm-bx7).

## Overview

`extract_pure_deep h` rewrites a hypothesis `h : (… ** ⌜P⌝ ** … ** ⌜Q⌝ ** …) s`
into a chain of `∧` applications by AC-normalising the `sepConj` chain and
applying `sepConj_pure_left` / `sepConj_pure_right` to bubble pure atoms
out. After the rewrite, the user can `obtain` directly without manually
walking the chain.

`extract_pure h` is retained as the shallow compatibility tactic. It performs
the original one-pass rewrite only, which lets existing proofs continue to
rely on their old local conjunction shape. New automation should prefer
`extract_pure_deep`.

We deliberately keep the surface small: callers say `extract_pure_deep h`,
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

/-! ### Assertion-level (`=`) pure-bubbling rewrites

The `sepConj_pure_mid_left` / `_mid_right` lemmas above are stated as
`∀ s, … s ↔ …`, so `simp only` will only fire them at the *outermost*
state-applied position. That's enough when the pure leaf sits at depth ≤ 1
in a right-associated chain, but for chains of length ≥ 4 with a pure
buried at depth ≥ 2 — e.g. `R₁ ** (R₂ ** (R₃ ** (⌜P⌝ ** R₅)))` — simp
cannot descend past the outer `**` because the rewrite pattern requires
a state argument.

The `_eq` variants below state the bubbling rules as `Assertion = Assertion`
equalities (no leading `∀ s`), so `simp` can apply them inside any nested
`**` subterm. Repeated application bubbles every pure leaf to the leftmost
position; once it lands at the top, the existing `sepConj_pure_left`
fires at the outer `s` and converts it to a `∧`.

Tracked under beads `evm-asm-22a` / GH #1435.
-/

theorem sepConj_pure_pure_eq {P Q : Prop} :
    (⌜P⌝ ** ⌜Q⌝) = ⌜P ∧ Q⌝ := by
  funext h
  rw [EvmAsm.Rv64.sepConj_pure_left]
  unfold EvmAsm.Rv64.pure
  apply propext
  constructor
  · intro h_pq
    exact ⟨h_pq.2.1, h_pq.1, h_pq.2.2⟩
  · intro h_pq
    exact ⟨h_pq.2.1, h_pq.1, h_pq.2.2⟩

theorem sepConj_pure_pure_left_eq {P Q : Prop} {R : Assertion} :
    (⌜P⌝ ** ⌜Q⌝ ** R) = (⌜P ∧ Q⌝ ** R) := by
  rw [← EvmAsm.Rv64.sepConj_assoc', sepConj_pure_pure_eq]

theorem sepConj_pure_mid_left_eq {P : Assertion} {Q : Prop} {R : Assertion} :
    (P ** ⌜Q⌝ ** R) = (⌜Q⌝ ** P ** R) := by
  rw [← EvmAsm.Rv64.sepConj_assoc', ← EvmAsm.Rv64.sepConj_assoc',
    EvmAsm.Rv64.sepConj_comm' P (⌜Q⌝)]

theorem sepConj_pure_mid_right_eq {P R : Assertion} {Q : Prop} :
    (P ** R ** ⌜Q⌝) = (⌜Q⌝ ** P ** R) := by
  rw [EvmAsm.Rv64.sepConj_comm' R (⌜Q⌝), ← EvmAsm.Rv64.sepConj_assoc',
    EvmAsm.Rv64.sepConj_comm' P (⌜Q⌝), EvmAsm.Rv64.sepConj_assoc']

theorem sepConj_pure_mid_assoc_eq {P R : Assertion} {Q : Prop} :
    ((P ** ⌜Q⌝) ** R) = (⌜Q⌝ ** P ** R) := by
  rw [EvmAsm.Rv64.sepConj_assoc']
  exact sepConj_pure_mid_left_eq

theorem sepConj_pure_head_assoc_eq {P : Prop} {Q R : Assertion} :
    ((⌜P⌝ ** Q) ** R) = (⌜P⌝ ** (Q ** R)) := by
  exact EvmAsm.Rv64.sepConj_assoc' (⌜P⌝) Q R

/-- Compatibility tactic with the original shallow extraction behavior.

    `extract_pure h` extracts pure atoms reachable by the state-applied `↔`
    lemmas, but it does not recursively rewrite nested assertion subterms.
    This preserves the old local shape expected by existing downstream proofs.
    New automation should generally use `extract_pure_deep`. -/
macro "extract_pure" h:ident : tactic =>
  `(tactic|
      simp only
        [ ← EvmAsm.Rv64.sepConj_assoc'
        , EvmAsm.Rv64.sepConj_pure_right
        , EvmAsm.Rv64.sepConj_pure_left
        , EvmAsm.Rv64.Tactics.sepConj_pure_mid_left
        , EvmAsm.Rv64.Tactics.sepConj_pure_mid_right
        , EvmAsm.Rv64.sepConj_emp_left'
        , EvmAsm.Rv64.sepConj_emp_right'
        ] at $h:ident)

/-- `extract_pure_deep h` rewrites a separation-logic hypothesis
    `h : (A₁ ** … ** Aₙ) s` into a `∧`-chain whose left conjuncts are
    the pure atoms (`⌜P⌝`) extracted from the chain and whose tail is
    the remaining resource assertion applied to `s`.

    Unlike `extract_pure`, this tactic also rewrites nested assertion
    subterms, so it can reach pure atoms buried under long framed `**` chains.

    After `extract_pure_deep h`, follow up with
    `obtain ⟨hP₁, …, hPₖ, hRest⟩ := h` to name the extracted purities and
    the resource tail.

    Example:
    ```
    example (s : PartialState) (R : Assertion) (P Q : Prop)
        (h : (R ** ⌜P⌝ ** ⌜Q⌝) s) : P ∧ Q := by
      extract_pure_deep h
      exact ⟨h.1, h.2.1⟩
    ``` -/
macro "extract_pure_deep" h:ident : tactic =>
  `(tactic|
      extract_pure $h:ident <;>
      try simp only
        [ EvmAsm.Rv64.Tactics.sepConj_pure_pure_left_eq
        , EvmAsm.Rv64.Tactics.sepConj_pure_pure_eq
        , EvmAsm.Rv64.Tactics.sepConj_pure_mid_assoc_eq
        , EvmAsm.Rv64.Tactics.sepConj_pure_head_assoc_eq
        , EvmAsm.Rv64.sepConj_pure_right
        , EvmAsm.Rv64.sepConj_pure_left
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

/-- Pure atom buried under a long framed chain. -/
example (s : PartialState) (P : Prop) (A B C D : Assertion)
    (h : (A ** (B ** (C ** (⌜P⌝ ** D)))) s) : P := by
  extract_pure_deep h
  exact h.1

/-- Pure atom behind the frame shape produced by branch framing. -/
example (s : PartialState) (P : Prop) (A B C D : Assertion)
    (h : ((A ** B ** ⌜P⌝) ** (C ** D)) s) : P := by
  extract_pure_deep h
  simp_all

/-- Multiple pure atoms interleaved with resources. -/
example (s : PartialState) (P Q : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** ⌜P⌝ ** R₂ ** ⌜Q⌝) s) : P ∧ Q := by
  extract_pure_deep h
  simp_all

end EvmAsm.Rv64.Tactics.ExtractPureTests
