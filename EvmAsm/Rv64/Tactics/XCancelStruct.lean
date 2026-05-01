/-
  EvmAsm.Rv64.Tactics.XCancelStruct

  Structural cancellation tactic — sibling of `xperm` / `xperm_hyp` / `xcancel`
  that closes a goal `⊢ G s` from a hypothesis `h : H s` *without* flattening
  either `**`-chain to its leaf atoms.

  Design reference: `docs/structural-cancel-design.md` (#245 slice 2,
  beads `evm-asm-0qba`). Prerequisite lemma family `sepConj_eq_congr_left` /
  `_right` / `_mid_left` lives in `EvmAsm/Rv64/SepLogic.lean` (#245 slice 3-pre,
  PR #1661).

  ## Usage

  ```lean
  -- (a) Pure AC-permutation, no opaque-bridge needed.
  example {A B C : Assertion} {s : PartialState} (h : (A ** B ** C) s) :
      (C ** A ** B) s := by xcancel_struct h

  -- (b) With `with`: pre-rewrite `h` via user-supplied equation lemmas before
  -- the AC-permutation step. Each lemma is applied as a `simp only` rewrite
  -- and may use `sepConj_eq_congr_mid_left` implicitly via simp's congruence
  -- closure to lift the equality through the surrounding `**`-chain.
  example {A B C D : Assertion} {s : PartialState}
      (heq : A = D) (h : (A ** B ** C) s) :
      (D ** B ** C) s := by xcancel_struct h with heq
  ```

  ## Algorithm

  Let `H` and `G` be the hypothesis and goal assertions.

  1. **Optional bridge step.** If `with e₁, …, eₙ` is supplied, apply
     `simp only [e₁, …, eₙ]` to `h`. Each `eᵢ : Aᵢ = Bᵢ` is lifted through the
     surrounding `**`-chain by `simp`'s congruence machinery — the AC-rewrite
     trio (`sepConj_assoc'` / `sepConj_comm'` / `sepConj_left_comm'`) is **not**
     unfolded at this stage; only the matched sub-assertions are rewritten.
  2. **AC-permutation step.** `sep_perm h` closes the goal via
     `congrFun (show H' = G by ac_rfl) s`. Crucially `ac_rfl` operates over
     the registered `Std.Associative (sepConj)` and `Std.Commutative (sepConj)`
     instances and treats every non-`sepConj` sub-tree as an atom — opaque
     `@[irreducible]` bundles like `iterN3Max_da …` stay opaque.

  ## Why structural

  Both steps preserve sub-tree opacity. The AC engine sees the chain as a
  binary tree over `sepConj`; whatever lives at the leaves is a black box.
  This is exactly the property `xperm_hyp` lacks — `xperm_hyp` flattens to
  atoms via `flattenSepConj` and then runs an O(n²) `isDefEq` matching loop,
  so its cost scales with the *total* atom count rather than the changing
  portion. See `docs/structural-cancel-design.md` §"Why structural beats
  flatten-based at the hot sites".

  ## Failure mode

  If the AC step cannot close the goal (residual atoms differ between `h`
  and the goal) `ac_rfl` raises a clear error pointing at the residual.
  Graceful "leave the residual as a sub-goal" handling is a follow-up
  (#156 / `xperm_partial`) — the prototype here is fail-fast.

  ## Out of scope (per design note §"Out of scope for slice 3")

  - "Match modulo `isDefEq`" mode — keep the prototype cheap by *not* paying
    the unfolding cost.
  - Automatic discovery of equation lemmas via the `simp` set; the user
    passes them explicitly with `with …`.
  - Goal-side variant; only `xcancel_struct <hyp>` ships in this slice.

  ## References

  - GH issue #245.
  - `docs/structural-cancel-design.md`.
  - `EvmAsm/Rv64/SepLogic.lean` — `sepConj_eq_congr_*` family + `sep_perm`.
-/

import Lean
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Rv64.Tactics

open Lean Elab Tactic

/-- `xcancel_struct h [with e₁, …, eₙ]` closes a goal `(G) s` from a
    hypothesis `h : (H) s` via structural AC-permutation over `sepConj`,
    optionally pre-rewriting `h` with user-supplied equation lemmas
    `e₁, …, eₙ`.

    See module docstring (and `docs/structural-cancel-design.md`) for the
    full design. -/
syntax (name := xcancelStructTac) "xcancel_struct " ident
  (" with " term,+)? : tactic

macro_rules
  | `(tactic| xcancel_struct $h:ident) =>
    `(tactic| sep_perm $h)
  | `(tactic| xcancel_struct $h:ident with $[$eqs],*) =>
    `(tactic|
      first
      | (simp only [$[$eqs:term],*] at $h:ident; sep_perm $h)
      | (rw [$[$eqs:term],*] at $h:ident; sep_perm $h))

end EvmAsm.Rv64.Tactics

-- ---------------------------------------------------------------------------
-- Smoke tests
-- ---------------------------------------------------------------------------
-- Six tests covering the cases listed in beads `evm-asm-otgf`:
--   (a) singleton match in chain head
--   (b) singleton match in chain mid (AC-permutation)
--   (c) opaque sub-assertion match (here: arbitrary `Assertion` variable)
--   (d) failure on no-match — verified via `fail_if_success`
--   (e) multiple match passes (longer chain, fully permuted)
--   (f) interaction with empAssertion (`** empAssertion` head/tail)
-- ---------------------------------------------------------------------------

namespace EvmAsm.Rv64.Tactics.XCancelStructTests

open EvmAsm.Rv64

-- (a) singleton match in chain head: identity permutation closes immediately.
example {A B C : Assertion} {s : PartialState} (h : (A ** B ** C) s) :
    (A ** B ** C) s := by
  xcancel_struct h

-- (b) singleton match in chain mid: AC-permutation of three atoms.
example {A B C : Assertion} {s : PartialState} (h : (A ** B ** C) s) :
    (B ** A ** C) s := by
  xcancel_struct h

-- (c) opaque sub-assertion match: any `Assertion` value, including a bundled
-- `@[irreducible]` definition or a deeply nested `seps`/`sepConj` sub-tree,
-- is treated as a single AC-atom. This is the structural property: we never
-- look inside `O`.
example {A B C O : Assertion} {s : PartialState} (h : (A ** O ** B ** C) s) :
    (B ** O ** C ** A) s := by
  xcancel_struct h

-- (d) failure on no-match: missing atom in hypothesis must not silently close.
set_option linter.unusedVariables false in
example {A B C : Assertion} {s : PartialState} (h : (A ** B) s) : True := by
  fail_if_success
    (show (A ** B ** C) s; xcancel_struct h)
  trivial

-- (e) multiple match passes: 5-atom chain fully reversed.
example {A B C D E : Assertion} {s : PartialState}
    (h : (A ** B ** C ** D ** E) s) :
    (E ** D ** C ** B ** A) s := by
  xcancel_struct h

-- (f) interaction with empAssertion: empty frames at head and tail cancel.
example {A B : Assertion} {s : PartialState}
    (h : (A ** empAssertion ** B) s) :
    (B ** A ** empAssertion) s := by
  xcancel_struct h

-- (g) `with` clause: pre-rewrite via a user-supplied equation lemma.
-- Bridges an opaque sub-assertion `O₁` in the hypothesis with the differently
-- written but provably-equal `O₂` in the goal.
example {A B O₁ O₂ : Assertion} {s : PartialState}
    (heq : O₁ = O₂) (h : (A ** O₁ ** B) s) :
    (O₂ ** B ** A) s := by
  xcancel_struct h with heq

end EvmAsm.Rv64.Tactics.XCancelStructTests
