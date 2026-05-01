# Structural cancellation — lemma family API design (#245 slice 2)

Status: design note / no Lean changes. Tracks beads `evm-asm-0qba`
(slice 2 of GH #245). Reads on top of `docs/structural-cancel-baseline.md`
(slice 1 / `evm-asm-h04i`) and `docs/xperm-scaling-2026.md`
(#265 slice 1 / `evm-asm-1bsj`).

## Goal

Add a hyp-side cancellation tactic — working name `xcancel_struct` — that
peels matched sub-assertions one at a time using equality-congruence over
`sepConj`, without ever flattening the chain to an atom list. This
preserves opacity of any sub-assertion the user wants opaque (e.g.
`iterN3Max_da …`, `loopIterPostN3Max_da …`, the bundled scratch-cell
records) while letting the proof author state goals in a different
nesting/order than the hypothesis.

`xcancel_struct` is **not** a replacement for `xperm_hyp`. It is a
sibling, optimized for the case where the changing portion of the
permutation is small (≤ 12 atoms per the baseline survey) and the rest
of the chain is opaque sub-assertions we'd rather keep `@[irreducible]`
during the cancellation step.

## Lemma shapes

All shapes live alongside the existing AC-rewrite trio
(`sepConj_assoc'`, `sepConj_comm'`, `sepConj_left_comm'`) in
`EvmAsm/Rv64/SepLogic.lean`. The proposed additions are pure
equality-congruence lemmas; no new operators, no new `Assertion`-level
machinery.

### (a) Equality-congruence base

```lean
theorem sepConj_eq_congr_left  {A B : Assertion} (h : A = B) (F : Assertion) :
    (A ** F) = (B ** F)
theorem sepConj_eq_congr_right {A B : Assertion} (F : Assertion) (h : A = B) :
    (F ** A) = (F ** B)
```

Both are one-line `h ▸ rfl` proofs. They are the structural analogue of
the atom-flattening step inside `xperm_hyp` — instead of reducing both
sides to an atom list, we lift an established equality `A = B` through
an arbitrary frame `F` *that does not need to be touched*.

### (b) Hoare-triple variant (frame rule, restated)

The existing `cpsTriple_frame` already provides `(P ⊢ Q) → ((P ** F) ⊢ (Q ** F))`
for our CPS-Hoare triples. The structural-cancel tactic does NOT need a
new frame rule; it operates at the assertion-equality level so that the
caller's existing `cpsTriple` chain (with its frame rules) consumes the
rewritten assertion via plain `rw`/`Eq.mpr`. Documenting this
explicitly so we don't accidentally duplicate the frame rule.

### (c) Peel-one-from-arbitrary-position

To peel a matched sub-assertion `A` from the *middle* of a `**`-chain we
combine (a) with the existing AC trio. The motion is:

```text
  hyp : (X ** A ** Y) s            goal : (A ** X ** Y) s
  ──────────────────────────────────────────────────────────
  rewrite hyp via sepConj_left_comm' on the (X ** (A ** Y))
  shape so A floats to the head, then `exact hyp`.
```

Symbolically, the lemma we'd actually call is `sepConj_left_comm'`
itself; `xcancel_struct`'s contribution is the *driver* that decides
which assoc/comm rotation to apply, not a new lemma.

### (d) Peel-frame builder

For the case where the goal contains a fresh sub-assertion
`A'` that the user has just proved equal to `A` (typical at the
end of a per-iteration loop step), we need:

```lean
theorem sepConj_eq_congr_mid_left
    {A B : Assertion} (X Y : Assertion) (h : A = B) :
    (X ** A ** Y) = (X ** B ** Y)
```

Proof: `sepConj_left_comm'` to rotate `A` to head, apply
`sepConj_eq_congr_left h`, rotate back. Two AC-rewrites + one base
congruence.

This is the *only* genuinely new lemma the family needs. Everything
else either already exists (`sepConj_assoc'`, `sepConj_comm'`,
`sepConj_left_comm'`) or is a straightforward `▸ rfl` corollary of
the base congruence.

### (e) Empty-frame elimination (already covered)

`sepConj_emp_left'` and `sepConj_emp_right'` already serve the
empAssertion folding step that `memBufferIs` and similar wrappers leave
behind. No new lemmas required.

## Tactic surface — `xcancel_struct`

Working syntax:

```text
xcancel_struct <hyp> [with <eqLemma>+]
```

Semantics:

1. Reads `hyp : H s` and goal `⊢ G s`.
2. Walks `H` and `G` as binary trees over `**`. For each leaf
   sub-assertion `A` in `H` that appears (up to syntactic equality, no
   `isDefEq` unfolding) somewhere in `G`, applies the
   sequence `sepConj_left_comm'`/`sepConj_assoc'` (driver-side, not
   user-visible) to rotate `A` to the head of both `H` and `G`, then
   `cases hyp; refine ⟨rfl_proof_for_A, ?_⟩` (figuratively — actually
   uses the equality-congruence path so `s` stays a single witness).
3. Repeats until either `H = G` syntactically (success: `exact hyp`),
   or no leaf can be peeled (failure: leaves a residual goal whose LHS
   and RHS are the unmatched portions of `H` and `G`).
4. The optional `with <eqLemma>+` argument supplies user-provided
   equalities (e.g. `iterN3Max_da_unfold`) which the tactic applies via
   `sepConj_eq_congr_mid_left` *before* peeling — this is how an opaque
   sub-assertion in the hypothesis can be matched against a different
   shape in the goal without unfolding it everywhere.

The driver itself is small: O(|H| · |G|) leaf comparisons using
`Expr.isAppOf`/`Expr.eq?` (no full `isDefEq` calls), AC-rotations done
by `simp only` with the three sepConj equality lemmas, congruence
applied via `Eq.mpr (sepConj_eq_congr_mid_left … h₁) hyp`.

### Failure mode

If after the loop neither side is empty, the tactic emits a
`xcancel_struct: residual` warning with both residuals shown, and
leaves a goal of shape `(<H-residual>) s ⊢ (<G-residual>) s` for
the user to discharge (typically by `xperm_hyp` on the small
remainder, or by `assumption` if the residuals are equal up to
already-rewritten address normalisation). This dovetails with #156
(`xperm_partial`): the structural cancel does the cheap, structural
peeling first, and `xperm_partial` then handles the small residual
where atom-flattening is acceptable.

## Interaction with `xperm` / `xperm_hyp`

| Situation | Recommended primary tactic |
|---|---|
| Both sides atom chains, ≤ 12 atoms total | `xperm_hyp` (existing, fast) |
| Either side contains a 17+-atom block of opaque sub-assertions | `xcancel_struct` first, then `xperm_hyp` on residual |
| Hypothesis carries pure leaves | `drop_pure` (existing, once `evm-asm-22a` lands), then either |
| Goal has a sub-assertion that is provably equal to one in hypothesis but written differently (e.g. `iterN3Max_da` vs `iterWithDoubleAddback…` post-`delta`) | `xcancel_struct … with <equation lemma>` |

The key property: `xcancel_struct` and `xperm_hyp` compose. The pilot
in slice 4 (LoopComposeN3.lean Site 1, ~35 atoms with a stable bundle of
~25) is the canonical case for `xcancel_struct` peeling the stable
bundle, then `xperm_hyp` on the ≤ 12-atom changing residual.

## Why structural beats flatten-based at the hot sites

From `docs/xperm-scaling-2026.md`'s tables the changing-atom set at
each hot site is ≤ 12, but the total atom count after flattening is
25–35. `xperm_hyp`'s O(n²) atom-matching loop runs over the whole
flattened chain on every call, so its cost scales with the total, not
the changing portion. `xcancel_struct` walks the trees structurally and
only does work proportional to the depth of the matched sub-tree, so
its cost scales with the changing portion. At 12 changing / 35 total
the structural tactic should run in roughly 12/35 ≈ 35% of the
`xperm_hyp` time at the same site.

The ≈ 130 `@[irreducible]` markers identified in the slice-1 baseline
as "exist solely to keep `xperm_hyp` cheap" can be dropped once
`xcancel_struct` is the primary cancellation tactic for those sites,
recovering readability and unblocking simp-driven definitional unfolds
that are currently gated by the `@[irreducible]` shield.

## Where flatten-based xperm still wins

Three cases keep `xperm_hyp` as the right tool:

1. **Mostly-singleton atoms (no opaque bundles)** — the cell-cluster
   compositions in `Compose/Base.lean` and the n=4 PhaseAB site
   (`xperm-scaling-2026.md` Site 2) where almost every atom is a single
   `↦ₘ` cell. Flatten-and-match is already cheap here; structural
   peeling adds rewrite overhead with no win.
2. **Heavily-permuted small chains (≤ 12 atoms total)** — the typical
   per-instruction proof step; `xperm_hyp` runs in a few milliseconds
   and structural peeling has no advantage.
3. **The drop_pure interaction** — `drop_pure` will keep using
   `xcancel` (its existing dependency) for the pure-leaf strip, then
   `xperm_hyp` on the resource tail. `xcancel_struct` is independent.

## Out of scope for slice 3 (prototype)

- A general "match modulo `isDefEq`" mode. Slice 3 limits matching to
  syntactic equality plus user-supplied equation lemmas. The `isDefEq`
  cost is what makes flatten-based `xperm_hyp` scale poorly; we keep
  the prototype cheap by *not* paying it.
- Automatic discovery of equation lemmas via the `simp` set. The user
  passes them explicitly with `with <lemma>+`. A `@[xcancel_struct]`
  attribute can be added later if patterns emerge.
- Goal-side variant. Slice 3 ships only `xcancel_struct <hyp>`. A
  goal-side `sep_perm`-like sibling is a follow-up if needed.

## Acceptance for slice 2 (this note)

- Design note merged at `docs/structural-cancel-design.md`.
- No Lean changes.
- Slice 3 (`evm-asm-otgf`) implements `xcancel_struct` per this design.
- Slice 4 (`evm-asm-bluw`) pilots on
  `EvmAsm/Evm64/DivMod/LoopComposeN3.lean`'s
  `divK_loop_n3_max_skip_skip_spec_within` (Site 1 of the baseline).

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
