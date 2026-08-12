# EvmAsm — Proof Patterns (deep reference)

Moved out of `AGENTS.md` to keep the agent guide compact. Load this when a proof you are
writing hits one of these symptoms; do **not** read end-to-end:

- **Postconditions explode under `xperm`** → §Bundling Postconditions with `let` Bindings.
- **Adapter signatures become unwieldy with deep let-chains** → §Adapter Signatures with Deep Let-Chains.
- **`linarith` fails on let-bound terms or `omega` blows up `maxRecDepth`** → §linarith vs omega for Let-Bound Terms / §Pure-Nat Sub-Lemmas.
- **End-to-end composition needs existential intermediates** → §End-to-End Composition with Existential Intermediates.
- **`xperm` hits scaling limits / atom-count cliffs** → §XPerm Scaling Limits and Sub-Assertion Bundling.
- **Double-addback (`_da`) postcondition shape needed** → §Double-Addback (_da) Postcondition Pattern.
- **Folded framed post fights `xperm`/`whnf`, or `extract_pure`/`drop_pure` misbehave** → §Folded Framed Posts.
- **Tempted to copy the `7 * (2 ^ 64 - 1) + 11` step bound into a new loop spec** → §The 7×(2^64−1)+11 Step-Bound Idiom.

Each section is self-contained — jump to the matching heading instead of reading top-to-bottom.

## The 7×(2^64−1)+11 Step-Bound Idiom

A number of `cpsTripleWithin` proofs carry a step bound of the form
`7 * (2 ^ 64 - 1) + 11` (or the shared `tailSteps` wrapper, used as
`1 + tailSteps` / `tailSteps + 5`). Measured population: 26–32 theorems
across 12 files (census at `89cdd641a`, GH #11461).

**What it means, and why it is sound.** The factor derives from the *machine
counter's width* — the loop decrements a 64-bit register, so the proof bounds
the trip count by the full `u64` range — **not from the data**. It is sound
because a `cpsTripleWithin` bound is an *upper* limit (`∃ k ≤ nSteps`), so any
sufficiently large bound closes.

**Stop-propagation clause.** A NEW proof must not copy this idiom without first
asking whether a concrete length bound is available for the input in scope.
Every existing site has its input (byte list / `listLen` / count) present as
hypotheses, so a data-driven bound of the form `7 * length + C` is available in
principle. **Open prerequisite (#11461):** no existing site carries a concrete
sub-`2^64` cap on its input length — only the memory-overflow guards — so there
is nothing to tighten *against* until someone decides where such a cap comes
from. Until that is settled: record the looseness, do not copy the idiom.

## Bundling Postconditions with `let` Bindings

When a composed spec's postcondition has many `let` bindings (e.g., shift
amounts, normalized limb values), wrap the entire postcondition — including
the `let` computations — in an `@[irreducible] def` returning `Assertion`.
This prevents Lean from repeatedly evaluating nested lets during type
elaboration.

### Pattern

**Define** the postcondition function in a shared file (e.g., `Compose/Base.lean`):

```lean
@[irreducible]
def myPost (sp param1 param2 ... : Word) : Assertion :=
  let derived1 := f param1
  let derived2 := g derived1 param2
  -- ... all computed values as let bindings ...
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ derived1) ** ... -- full assertion chain
```

**Provide an unfold lemma** (for consumers that need the expanded form):

```lean
theorem myPost_unfold (sp param1 param2 ... : Word) :
    myPost sp param1 param2 ... =
    let derived1 := f param1
    ... -- same body as the def
    := by delta myPost; rfl
```

**Use in theorem signatures** — the `let` bindings disappear from the type:

```lean
-- BEFORE (11 let bindings in the type, slow elaboration):
theorem my_spec ... :
    let shift := (clzResult b3).1
    let anti_shift := ...
    ... 9 more lets ...
    cpsTriple ... precond (expanded 30-atom postcondition)

-- AFTER (compact type, fast elaboration):
theorem my_spec ... :
    cpsTriple ... precond (myPost sp n_val (clzResult b3).1 a0 a1 a2 a3 ...)
```

**Proof changes** — define the `let` bindings locally and unfold at the end:

```lean
theorem my_spec ... :
    cpsTriple ... precond (myPost sp n_val shift_arg ...) := by
  -- Local lets for use in intermediate composition steps
  let shift := shift_arg
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  ... -- same let bindings as in myPost body
  -- ... composition steps (unchanged) ...
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta myPost; xperm_hyp hq)  -- delta unfolds @[irreducible]
    hFull
```

### Why `@[irreducible]`

- `xperm` uses reducible transparency, so even a plain `def` is opaque to it.
  `@[irreducible]` adds safety: `simp` and `whnf` at default transparency also
  won't accidentally unfold it.
- `delta` ignores transparency and always unfolds — use it in the proof's
  final `cpsTriple_weaken` callback.
- Matches the existing `phaseB_zeroed_mem` pattern in `PhaseAB.lean`.

### Scaling: external weaken lemma

As compositions grow, the inline `delta myPost; xperm_hyp hq` in each
proof's `cpsTriple_weaken` callback may become a bottleneck. To avoid
repeating this work in every consumer, extract the implication as a
standalone lemma (name it `_weaken` to match the `cpsTriple_weaken` /
`cpsBranch_weaken` naming from #331):

```lean
theorem myPost_weaken (sp param1 ... : Word) (h : PartialState)
    (hq : (expanded_postcondition) h) :
    myPost sp param1 ... h := by
  delta myPost; xperm_hyp hq
```

Then each theorem's final step becomes:

```lean
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => myPost_weaken sp param1 ... h hq)
    hFull
```

This pays the `delta + xperm` cost once (when the lemma is checked) rather
than in every theorem that produces `myPost`. Place the weaken lemma
next to the `def` and `_unfold` lemma in the shared file.

### When to apply

Apply this pattern when a theorem's postcondition has **3+ `let` bindings**
that compute derived values used in the assertion chain. The canonical example
is `loopSetupPost` in `Compose/Base.lean` (11 let bindings, used by 8 theorems).

## Adapter Signatures with Deep Let-Chains (Algorithm Intermediates)

For **stack-level adapters** that expose runtime-computed intermediate
values via `let` chains (e.g., `let ms := mulsubN4 ...; let ab := addbackN4
...; let un{i}Out := if carry = 0 then ab'.{i_low} else ab.{i_low}`),
keep the goal small by wrapping each natural intermediate as a separate
`@[irreducible] noncomputable def` rather than letting the proof state
materialize the entire chain inline.

The DivMod call+addback BEQ adapter is the canonical example
(`output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm`). A first
attempt with the inline let-chain in the signature yielded a 246-line
proof that fought 200k-heartbeat `whnf` timeouts in the final fold; a
restart with per-intermediate irreducibles cut it to ~50 lines and
closed the single-addback case cleanly.

### Pattern (3 components per intermediate)

For each algorithm intermediate value `X`:

1. **Irreducible def** capturing the computation as an opaque term:

   ```lean
   @[irreducible]
   noncomputable def algCallAddbackBeqUn0Out (a b : EvmWord) : Word :=
     let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     ... -- full let-chain
     if carry = 0 then ab'.1 else ab.1
   ```

2. **Unfolding lemma** for consumers that need the inline form:

   ```lean
   theorem algCallAddbackBeqUn0Out_unfold {a b : EvmWord} :
       algCallAddbackBeqUn0Out a b = (let shift := ...; ... if-then-else) := by
     show algCallAddbackBeqUn0Out a b = _
     unfold algCallAddbackBeqUn0Out
     rfl
   ```

3. **Bridge lemma** connecting the irreducible to a derived form (e.g.,
   the `single-addback` case where `un{i}Out = post1Limb{i}` because
   `addbackN4`'s low 4 outputs are independent of the `u4_new` parameter):

   ```lean
   theorem algCallAddbackBeqUn0Out_eq_post1Limb0_of_single_addback
       (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
       algCallAddbackBeqUn0Out a b = algCallAddbackBeqPost1Limb0 a b := by
     rw [algCallAddbackBeqCarry_unfold] at hcarry
     unfold algCallAddbackBeqUn0Out algCallAddbackBeqPost1Limb0
     simp only []; rw [if_neg hcarry]; rfl
   ```

### Adapter signature pattern

The adapter's conclusion uses `let` to alias the irreducibles, keeping
the printed type compact while letting consumers refer to them:

```lean
theorem output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm
    (sp : Word) (a b : EvmWord) (...) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let un0Out := algCallAddbackBeqUn0Out a b
    let un1Out := algCallAddbackBeqUn1Out a b
    ...
    (((sp + 32) ↦ₘ ((un0Out >>> shift) ||| (un1Out <<< (64 - shift)))) **
     ...) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  intro shift un0Out un1Out un2Out un3Out
  by_cases hcarry : algCallAddbackBeqCarry a b = 0
  · sorry  -- alternative branch
  · rw [show un0Out = algCallAddbackBeqPost1Limb0 a b from ...,
        show un1Out = algCallAddbackBeqPost1Limb1 a b from ...,
        ...]
    exact (evmWordIs_sp32_limbs_eq sp ...).symm
```

### Caller adaptation

When an adapter's signature changes from inline `let un{i}Out := if-then-else`
to irreducible-bundled `let un{i}Out := algCallAddbackBeqUn{i}Out a b`,
**callers must fold their inline forms back to the irreducibles**. Without
this fold, `xperm_hyp` (which compares atoms syntactically) fails to match
the inline-form atoms in the hypothesis with the irreducible-form atoms
introduced by `rw [adapter.symm]`.

```lean
intro h hq
simp only [fullModN4CallAddbackBeqPost_unfold, denormModPost_unfold] at hq
-- Fold hq's inline un{i}Out forms to the irreducible Un{i}Out names
-- so they match the adapter's new signature.
simp only [← algCallAddbackBeqUn0Out_unfold, ← algCallAddbackBeqUn1Out_unfold,
           ← algCallAddbackBeqUn2Out_unfold, ← algCallAddbackBeqUn3Out_unfold] at hq
...
rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
...
xperm_hyp hq
```

### Symptoms that warrant the irreducible-bundle restructure

If a stack-level adapter's proof exhibits any of these, the let-chain
is too deep and the proof state needs irreducible bundling:

- `rw [← unfold_lemma]` and `simp only [← unfold_lemma]` **silently no-op**
  (succeed without firing) — the rewriter can't match the let-chain RHS
  against the goal's zeta-reduced form.
- `exact (some_helper).symm` produces a `Type mismatch` where the actual
  and expected types **look identical** in the printed output but differ
  in projection-index spacing or implicit args.
- `convert (some_helper).symm using N` (any `N`) hits a 200k-heartbeat
  timeout in `whnf` during defeq slack.
- Diagnostic by `diff` of the error's "actual" and "expected" terms
  reveals the structures are the same up to subtle nested-shape
  differences that no `simp`/`rw` reconciles.

### Why irreducibles work where `set` doesn't

`set X := body with hX_def` creates a let-bound local + the equation
`hX_def : X = body`, but it only matches occurrences of `body` in the
goal **syntactically**. After `dsimp only []` zeta-reduces the goal,
`set` against parent-shaped expressions silently fails (no occurrences
to bind). Irreducible defs sidestep this: their term is opaque from
the outside, so subsequent `rw`/`simp`/`xperm` see one atom rather
than navigating the let-chain.

### Sub-lemma split

Pair the irreducible bundling with **sub-lemma extraction**. A focused
sub-lemma takes the irreducibles as inputs and produces a small
4-tuple of per-limb facts (e.g.,
`mod_n4_call_addback_beq_single_addback_post1_limbs_close`):

```lean
theorem mod_n4_..._post1_limbs_close (a b : EvmWord) (...)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    (EvmWord.mod a b).getLimbN 0 =
      ((algCallAddbackBeqPost1Limb0 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb1 a b) <<< (64 - s)) ∧
    ... := by
  intro s
  have h_wrapper := parent_post1Val_eq_amod_pow_s_of_single_addback ...
  rw [algCallAddbackBeqPost1Val_eq_val256_limbs] at h_wrapper
  ...
  exact denorm_4limb_eq_mod_of_val256_eq_amod_pow_s ...
```

The adapter's proof body then collapses to a single `rw` of the
bridges plus an `exact` of `evmWordIs_sp32_limbs_eq.symm` applied to
the sub-lemma's output.

### When to apply

Apply this pattern when an adapter's conclusion has **deep let-chains
mixing if-then-else and recursive function calls** (e.g., `mulsubN4`
inside `addbackN4` inside `if`), and a first attempt at the proof body
hits any of the symptoms listed above. Spending the iteration on
irreducible bundles + sub-lemmas pays for itself by avoiding the
"refactoring tax" of multiple failed `simp`/`rw`/`exact` attempts.

## linarith vs omega for Let-Bound Terms

When a goal mixes locally-introduced `let` bindings (e.g. via `intro`) with
hypotheses obtained by applying a separately-stated theorem whose conclusion
unfolds its own lets, `omega` may fail even when the algebra is trivial. The
two sides see syntactically distinct copies of the same definitionally-equal
expression (`(uLo >>> 32).toNat` vs `div_un1.toNat` where
`div_un1 := uLo >>> 32`), and `omega` treats them as opaque, unrelated atoms.

**Try `linarith` first** in this regime. It does a looser syntactic match and
often closes the goal without any extra rewrites:

```lean
intro dHi dLo div_un1 q1 ... q1c
have h_range := some_range_lemma uHi uLo vTop ...
obtain ⟨h_lower, h_upper⟩ := h_range
-- h_lower has the unfolded `(uLo >>> 32).toNat` form;
-- the goal's `div_un1.toNat` is the local-let form. omega chokes; linarith doesn't.
have h_eq : q1c.toNat = ... + 1 := by linarith
```

Reach for `omega` when the reasoning is genuinely Presburger (modular
arithmetic, divisibility); reach for `linarith` when the reasoning is plain
linear inequality and the only friction is term-shape mismatch on
let-bindings. If both fail, fall through to **Pure-Nat Sub-Lemmas** (next
section) — extracting a focused helper sidesteps the let-binding issue
entirely by passing concrete `Nat` values across the call boundary.

## Pure-Nat Sub-Lemmas for omega/maxRecDepth Avoidance

When a proof in a theorem with **deep let-chains and many opaque
non-linear products** (e.g., `(q + 1) * dHi`, `(q + 2) * dLo`) hits
`omega`'s `maxRecDepth` limit, factor the algebraic core into a
**private pure-Nat sub-lemma** with explicit `set` aliases for the
non-linear products.

### Symptoms

- `omega` produces "maximum recursion depth has been reached" inside a
  `have` block, even after splitting the proof.
- The constraint set in `omega`'s error message contains many
  independent product variables (e.g., `g := (q_true + 1) * dHi.toNat`,
  `i := (q_true + 2) * dHi.toNat`) that omega treats as opaque.
- The ambient theorem has **20+ let-bound variables** (full algorithm
  state introduced via `intro`).

### Why omega struggles

`omega` is a decision procedure for **linear** integer arithmetic. When
the ambient context has many non-linear products as terms (`a * b` where
both factors involve variables), omega treats each product as a fresh
variable and tries to discover linear relationships between them. With
many products and many constraints, this exploration can hit elaboration
limits.

### Pattern

For each algebraic deduction that hits `maxRecDepth`, extract a private
helper that takes **only the relevant Nat variables** and uses `set`
aliases inside to keep the constraints linear:

```lean
private theorem my_arith_helper (u4 A B div_un1 : Nat)
    (h_x_lt : u4 * 2^32 + div_un1 < A * 2^32 + B)
    (h_A_le_u4 : A ≤ u4)
    (h_B_bound : B + 2^32 ≤ 2^64) :
    u4 - A < 2^32 := by
  set X := u4 * 2^32 with hX
  set Y := A * 2^32 with hY
  have h_sub_mul : (u4 - A) * 2^32 = X - Y := by
    rw [hX, hY, Nat.sub_mul]
  have h_Y_le_X : Y ≤ X := Nat.mul_le_mul_right _ h_A_le_u4
  have h_step : (u4 - A) * 2^32 < B + 2^32 := by
    rw [h_sub_mul]; omega
  set Z := (u4 - A) * 2^32 with hZ
  by_contra h_ge
  push Not at h_ge
  have h_mul : 2^32 * 2^32 ≤ Z := by
    rw [hZ]; exact Nat.mul_le_mul_right _ h_ge
  have h_pow_eq : (2^32 * 2^32 : Nat) = 2^64 := by decide
  omega
```

### Why this works

- The sub-lemma's **isolated context** has only the few hypotheses it
  needs, so omega's search space is bounded.
- `set X := ...` with `with hX` introduces a local fvar plus an equation;
  omega sees `X` as a single variable and `X = ...` as one linear
  constraint, sidestepping the non-linear product entirely.
- Pre-computing `Nat.mul_le_mul_right _ h_A_le_u4` as `Y ≤ X` (linear
  fact between aliases) gives omega exactly the linear hypothesis it
  needs.
- The main theorem invokes `my_arith_helper u4.toNat A B div_un1.toNat ...`,
  passing concrete Nat values rather than wading through let-zeta.

### When to apply

When a proof body:
1. Has 20+ let-bound variables (typical for algorithm-state-heavy proofs
   like `div128Quot_v2` Phase-1).
2. Contains an algebraic deduction that's **mathematically simple but
   non-linear** (e.g., `(u4 - A) * 2^32 < 2^64` from inequalities
   involving products).
3. Hits `maxRecDepth` in `omega` despite being structurally correct.

Following the Critical Rule "**don't add `set_option maxRecDepth`**" —
extract a pure-Nat helper instead. The helper amortizes the algebraic
work and keeps the main proof readable.

### Canonical example

`phase1b_2nd_guard_arith` in `Evm64/DivMod/SpecCallAddbackBeq.lean` is
the canonical reference. It captures Knuth's TAOCP §4.3.1 rhat bound
under overshoot=2 (`u4 - (q_true + 1) * dHi < 2^32`) as a pure-Nat
statement, allowing the consumer
`div128Quot_v2_phase1b_2nd_guard_under_runtime` to discharge the
algebra in one line. The pattern was extracted after a first proof
attempt repeatedly hit `maxRecDepth` despite restructuring (changing
`set` calls, splitting `have` blocks) within the main theorem body.

Sibling examples in the same file: `conj2_arith`,
`un21_lt_vTop_arith`, `un21_toNat_untruncated_arith` — each isolates
a focused pure-Nat algebraic claim invoked by a Word-level theorem.

## End-to-End Composition with Existential Intermediates

When composing specs where an intermediate postcondition has existentials (e.g., `loopBodyPostN4` which wraps computed values in `∃`), standard `cpsTriple_seq_perm_same_cr` doesn't work because the second spec's precondition depends on the existential witnesses.

### Approach: Unfold `cpsTriple` directly

```lean
show cpsTriple base end_ cr P R
intro F hF st hcr hPF hpc
-- Execute first half
obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF st hcr hPF hpc
-- Destructure holdsFor and sep conj
obtain ⟨h_full, hcompat1, ...⟩ := hQF
-- Expand existential def (e.g., loopBodyPostN4)
dsimp only [loopBodyPostN4] at hLP
obtain ⟨x2v, ..., hLP_atoms⟩ := hLP
-- Now have concrete values → instantiate second spec
have h2 := second_spec ... x2v ...
-- Apply second spec with combined frame
obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := h2 (LEFTOVER ** F) ...
-- Chain steps
exact ⟨k1 + k2, s2, stepN_add_eq ..., hpc2, ...⟩
```

### Key techniques

1. **`cpsTriple_seq_ex_same_cr`** (in `DivN4Full.lean`): Helper lemma for composing `cpsTriple s m cr P (fun h => ∃ v, Q v h)` with `∀ v, cpsTriple m e cr (Q v) R`. Handles the `holdsFor`/`sepConj` plumbing internally.

2. **`rw [← sepConj_assoc']`**: Re-associates `P ** (Q ** F)` to `(P ** Q) ** F` — essential for separating the frame F from the combined assertion when constructing the postcondition existentials.

3. **`intro_lets` at hypothesis**: Expands let-bindings from spec postconditions (e.g., `anti_shift`, `u0'`) into local definitions that can be used as existential witnesses.

4. **Combined frame approach**: When applying a `cpsTriple` spec directly (after unfolding), use `hDE (LEFTOVER ** F) hLOF_pcFree s1 ...` to pass both leftover atoms AND the original frame F as the frame parameter. This avoids a separate `cpsTriple_frameR` step and the resulting 36+ atom xperm.

5. **Address canonicalization for `j=0`**: The `j0_*_addr_eq` lemmas convert `u_base`-relative addresses (from `loopBodyPostN4`) to canonical `sp + signExtend12 XXXX` form. Also need `signExtend12_32/40/48/56` to convert `sp + signExtend12 32` to `sp + 32`. Apply these with `simp only [...] at hLP` after `dsimp only [loopBodyPostN4]`.

6. **`pcFree` for combined frames**: The `pcFree` tactic can't see through `let`/`set` definitions. Either inline the frame assertion or use `pcFree; exact hF` when the frame ends with an abstract `F`.

### Import cycle prevention

`DivN4Full.lean` imports both `LoopBodyN4` and `FullPath.lean`. Since `LoopBody.lean` → `Compose.lean` already forms a chain, do NOT add `DivN4Full` to `Compose.lean`'s imports — it would create a cycle. `DivN4Full` stands alone.

## XPerm Scaling Limits and Sub-Assertion Bundling

`xperm_hyp` is O(n^2) in the number of atoms, with each pair comparison
potentially triggering deep WHNF reduction. At ~36 atoms with complex
sub-expressions (e.g., `iterN3Call` + `iterN3Max` iteration results), this
can exceed the 200k heartbeat budget even in a dedicated theorem.

### Symptoms

- `xperm_hyp hp` times out in perm/consequence callbacks
- The same proof structure works for simpler atom expressions (e.g., all
  `iterN3Max`) but fails when atom values involve mixed function calls
- The let-binding chain itself passes `sorry` tests — the timeout is
  specifically in the `xperm` atom matching

### Solution: bundle sub-assertions as `@[irreducible] def`

Wrap logical groups of atoms into `@[irreducible] def`s so that `xperm`
sees a few opaque atoms instead of 36 individual ones:

```lean
-- Instead of 20 flat atoms for denorm input:
@[irreducible]
def denormInputN3 (sp shift u0 u1 u2 u3 q0 q1 b0' b1' b2' b3' : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** ... ** ((sp + 56) ↦ₘ b3')

-- And 16 flat atoms for the frame:
@[irreducible]
def denormFrameN3 (sp base r0_u4 r1_u4 r0_q a0 a1 a2 a3 b2' u2 : Word) : Assertion :=
  ((sp + 0) ↦ₘ a0) ** ... ** (sp + signExtend12 3944 ↦ₘ div128Un0 u2)
```

Then `xperm` only matches 2-3 opaque atoms instead of 36, avoiding
the O(n^2) blowup. Each sub-assertion is unfolded via `delta` only
when needed (e.g., in the denorm epilogue's own pre-weakening callback).

### When to apply

When a composition has **30+ atoms** in the intermediate assertion and
the atom values involve **two or more complex functions** (e.g., mixed
`iterN3Call`/`iterN3Max` results). Same-function compositions (all
`iterN3Max`) tend to stay within budget because `isDefEq` is faster
when comparing structurally similar expressions.

### Guideline for new compositions

- Keep each `xperm` call to **≤ 20 atoms** with complex sub-expressions
- For multi-iteration loops, define per-iteration postconditions as
  `@[irreducible] def`s (already done: `loopBodyN3SkipPost`, etc.)
- For full-path compositions, also bundle the denorm input and frame
  groups as `@[irreducible] def`s

## Double-Addback (_da) Postcondition Pattern

The double-addback fix (BEQ instruction after addback) introduces a second
addback path when carry=0. The `_da` postconditions use `@[irreducible]`
definitions at two levels — the iteration function and the postcondition —
with equation lemmas bridging between the raw spec output and the collapsed
postcondition. This keeps **producers** cheap (single `rw`) and
**consumers** cheap (single `xperm_hyp`, no case-split).

### Architecture

```
iterN3Max_da          @[irreducible]  — collapsed 6-tuple with double-addback
loopIterPostN3Max_da  @[irreducible]  — loopExitPostN3 with iterN3Max_da values
```

**Producer** (per-iteration _da spec, e.g., `divK_loop_body_n3_max_unified_j1_da_spec`):
- Branches on borrow (`by_cases hb`), dispatches to beq or skip sub-spec
- Wraps postcondition via `rw [← loopIterPostN3Max_da_addback ... hb]` or `_skip`
- For j=0 call-path: also `rw [loopBodyN3CallAddbackBeqPost_eq_J]` to bridge
  the j=0-specific variant to the generic-j equation lemma

**Consumer** (per-path composition, e.g., `divK_loop_n3_max_max_da_spec`):
- `delta loopIterPostN3Max_da loopExitPostN3 loopExitPost at hp` — expands
  the `@[irreducible]` postcondition to raw atoms with opaque
  `(iterN3Max_da ...).X` projections
- `simp only [] at hp ⊢` — normalizes let-bindings
- Address rewrites + `xperm_hyp hp` — single permutation pass, no case-split

### Equation lemmas (in LoopDefs.lean)

Each postcondition has two equation lemmas proved once:

```lean
theorem loopIterPostN3Max_da_addback (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (hb : BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) ...)) :
    loopBodyN3AddbackBeqPost sp j (signExtend12 4095) v0 ... u_top =
    loopIterPostN3Max_da sp j v0 ... u_top := by
  delta loopIterPostN3Max_da iterN3Max_da iterWithDoubleAddback
        loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
  unfold mulsubN4_c3 at hb; simp only [if_pos hb]; split <;> rfl
```

The `split <;> rfl` handles the inner carry=0 conditional: after resolving
the outer borrow `if`, both sides have the same `if carry = 0 then ... else ...`
structure. `split` case-splits on carry, then `rfl` closes each branch since
the tuple projections match the conditional values.

### Why this scales

- **No heartbeat issues**: Consumers never expand `iterN3Max_da` (it's
  `@[irreducible]`), so `simp` and `xperm_hyp` see small terms
- **Single xperm_hyp**: The connecting function in multi-iteration compositions
  does ONE permutation pass on ~25 atoms with opaque iter_da projections,
  identical in cost to the non-_da version
- **Equation lemmas amortize**: The `delta + simp + split <;> rfl` work is done
  once per equation lemma, not repeated in every consumer

### Scratch cell handling for unified postconditions

When the outermost iteration (j=2 for N=2, j=3 for N=1) takes the call path,
it overwrites scratch cells with div128 values. The unified postcondition
(`loopN2UnifiedPost_da`) must conditionally set scratch values:

```lean
let scratch_ret := if bltu_2 then (base + 516) else ret_mem
let scratch_d   := if bltu_2 then v1 else d_mem
...
```

After `cases bltu_2`, use `simp only [Bool.false_eq_true, ↓reduceIte]` (max path)
or `simp only [ite_true]` (call path) to resolve these conditionals before
`xperm_hyp`.

### BLTU projection for N=k

The BLTU condition for iteration N=k compares `un_{k-1}` (the (k-1)-th
u-component) with `v_{k-1}`. In the 6-tuple `(q, un0, un1, un2, un3, u4)`, projections are:
`.1`=q, `.2.1`=un0, `.2.2.1`=un1, `.2.2.2.1`=un2, `.2.2.2.2.1`=un3, `.2.2.2.2.2`=u4.
The BLTU compares `un_{N-1}` with `v_{N-1}`:
- N=1: compare `un0` = `.2.1` with `v0`
- N=2: compare `un1` = `.2.2.1` with `v1`
- N=3: compare `un2` = `.2.2.2.1` with `v2`

Be careful with the projection depth — off-by-one here causes type mismatches
that are hard to diagnose (the error appears at the `hbltu` application site,
far from the definition).


## Folded Framed Posts: DivMod-Scale xperm/whnf Blowups and Framed-Pure Extraction

(Moved from AGENTS.md "Critical Rules" to keep the agent guide compact;
tracking issue for the pure-extraction tactic gaps:
https://github.com/Verified-zkEVM/evm-asm/issues/7174.)

### When DivMod postconditions explode under `xperm` or kernel `whnf`

Fold the postcondition before trying harder tactics. Put the final register/memory assertion spine behind a small `@[irreducible]` helper such as `...PostCore`, parameterized by the final values that the branch proof should expose. If the public post has a deep body let-chain, add a second folded helper such as `...PostFromBody` that takes already-computed intermediates; the public `...Post` should compute the lets and delegate to the helper. In branch bridge proofs, use `change` to refold the expanded target to the helper with local names, simplify only the relevant `if_pos`/`if_neg`, then unfold only the small core immediately before `xperm_hyp`. Split repeated bridge obligations into named lemmas for fresh heartbeat budgets. Use `lean_goal` at the failing line to confirm the target is folded; if it prints a huge `BitVec.toNat 32` or nested-let/nested-if term, fold first instead of running `xperm` on the expanded goal.

### When extracting framed pure facts in bridge posts

Inspect the shape with `lean_goal` before repeatedly applying `drop_pure` or `extract_pure`. Framed pures may remain behind an extra `sepConj` layer, so remove one layer at a time with small local rewrites (`rw [sepConj_assoc']`, `simp only [sepConj_pure_mid_left]`) and `obtain` the pure fact you need. Broad `simp` or blind repeated extraction can expand the folded post again or destruct useful `sepConj` structure.
### When `extract_pure`, `drop_pure`, or `xperm_pure` struggle on a folded framed post

Avoid broad pure-extraction tactics on the whole post if they expand the folded helper, trigger kernel `whnf`, leave `xperm` atom-count mismatches, or report an expected-type/free-variable error. First extract only the outer pure fact you need, then rewrite the specific remaining pure assertion to `empAssertion` with a local extensional proof and simplify the emp frame before calling `xperm_hyp`. Shape:

  ```lean
  extract_pure hp
  obtain ⟨hp, h_pure⟩ := hp
  rw [show (⌜P⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p
      exact h_p.1
    · intro h_empty
      exact ⟨h_empty, h_pure⟩] at hp
  simp only [the relevant sepConj_emp lemma] at hp
  xperm_hyp hp
  ```

  Keep `EvmAsm.Rv64.pure` qualified in the unfold so Lean does not choose an unrelated `pure`, and keep the target folded until the final local rewrite. Tracking issue: https://github.com/Verified-zkEVM/evm-asm/issues/7174.
