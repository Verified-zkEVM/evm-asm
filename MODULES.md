# MODULES.md — Lean module-system conventions

This document is the single source of truth for how this repo uses the Lean 4.33
module system. Read it before adding a `.lean` file, before adding an import to
an existing one, and before deciding whether a definition needs `@[expose]`.

`CLAUDE.md` and `AGENTS.md` link here from their conventions sections — do not
duplicate this content elsewhere.

---

## 1. Why we are doing this

Without the module system, Lean has no notion of a module *interface* separate
from its contents, so editing any file re-elaborates that file's entire
reverse-import cone. Measured on this tree:

| quantity | value |
| --- | --- |
| mean cone | 113 modules (median 20, p90 337, max 2873 at `Rv64.Word`) |
| expected invalidation per file touch, churn-weighted over 60 days | **143 modules / 0.14 GB** |
| share of (commit, file) touches that change no declaration, import, or attribute | **≈50 %** |

That last row is the point. Under the module system a public theorem's **proof
term is not part of the interface** — three different proofs of one statement
produce a byte-identical `.olean`. So roughly half of this repo's edits go from
re-elaborating 143 modules to re-elaborating 1.

What changes an interface is *adding a declaration*, not rewriting a proof.
`simp [f]` / `unfold f` is not a counterexample: it **realizes the equation
lemma** `f.eq_1`, which is an added public declaration — one-shot per definition,
then stable again.

Run `python3 scripts/import-graph-metrics.py --private-cone` to see the
conservative cone beside the interface-invalidation cone. They are equal for an
unmigrated module and diverge as migration lands.

---

## 2. The required file header

Every file under `EvmAsm/` looks like this, immediately after its banner:

```lean
/-
  EvmAsm.Rv64.Example

  ... existing banner prose ...
-/

module

public import EvmAsm.Rv64.Basic
public import EvmAsm.Rv64.SepLogic

@[expose] public section

namespace EvmAsm.Rv64
```

Generate it with `scripts/migrate-module-system.py`; do not hand-write it. The
script is idempotent, so running it on a file that already has a header is a
no-op.

`module` must precede the first import. `@[expose] public section` must follow
the last one — an import after it does not parse (*"invalid 'import' command, it
must be used in the beginning of the file"*).

## 3. `public import` vs plain `import`

**Today the answer is always `public import`.** The migration deliberately
preserves existing re-export behaviour rather than trying to get the import
graph right at the same time as converting 3000 files. Mathlib does the same
(25482 `public import` vs 628 plain), so this is a defensible resting state, not
a half-finished job.

The distinction, for when the narrowing pass starts:

- `public import X` — X's declarations are re-exported. Anything importing *this*
  module also sees X.
- `import X` — X is used here but not re-exported. A downstream consumer that
  needs X must import it itself.

Plain `import` is the better default *in principle*: it is what stops a module's
API surface from being a transitive accident. **49.3 % of this tree's import
edges (7042 of 14278) are already implied by a sibling import** — that is the
headroom, and `lake shake --add-public --fix` computes the demotion. Until that
pass runs, do not hand-demote imports in ordinary PRs: a demotion is a real
change to what downstream files can see, and it belongs in a batch that is
measured as a batch.

## 4. `meta import`, and why files carry both forms

A file with any metaprogramming — `#guard`, `#eval`, `initialize`, `syntax`,
`elab`, `MetaM`, `register_simp_attr` — needs its imports mirrored at meta level:

```lean
public import EvmAsm.Rv64.Execution
meta import EvmAsm.Rv64.Execution
```

Both lines, for the same module. This looks redundant and is not:

- `public meta import X` re-exports X's declarations **as meta**, so an ordinary
  downstream consumer breaks with *"may not access declaration `step` imported as
  `meta`"*.
- But a `meta` definition in this file **cannot see X at all** unless X is
  imported at meta level: *"Invalid `meta` definition, `instBEqReg` is not
  accessible here"*.

The public import carries the ordinary re-export; the plain `meta import` grants
local elaboration-time access only. Mathlib carries the same pair — see
`Mathlib/Order/Interval/Lex.lean`, which meta-imports `Mathlib.Order.Interval.Basic`
alongside its public import of the same module, for `#eval`.

One special case: `initialize` + `registerSimpAttr` also needs
`public meta import Lean.Meta.Tactic.Simp.Attr`, which is normally not among the
file's own imports. The converter adds it.

## 5. `@[expose]` — the contract about what proofs may unfold

`@[expose] public section` puts every definition **body** in the file into the
module interface, so downstream proofs can see through it. That was the right
default for the migration — it preserved pre-migration behaviour — but it is not
the right default afterwards, and narrowing it is what the exposure pass does.

⚠️ **The operation is `@[expose] public section` → `public section`.** Never
delete the line: `public section` is what exports the declarations at all.

### What it actually costs, measured

`Stateless/SpecRef/IncrementalMptWrite.lean` (50 `def`s), same
semantics-preserving edit to one definition body, public `.olean.hash` (which is
what Lake keys downstream invalidation on):

| exposure | body | public hash | downstream |
| --- | --- | --- | --- |
| `@[expose] public section` | original | `9209185754286df7` | — |
| `@[expose] public section` | edited | `a2b0a9a51c9f7d99` | **whole cone rebuilds** |
| `public section` | original | `dfbd7d1b90979cfb` | — |
| `public section` | edited | `dfbd7d1b90979cfb` | **nothing rebuilds** |

Un-exposing that one file also cut its public `.olean` from 555 080 to 197 432
bytes — **−64 %** — and the public olean is what every downstream module loads.

### The rule

A definition needs `@[expose]` iff **another module reasons about its value**:
`unfold f`, `simp only [f]`, `rw [f]`, `delta f`, or `rfl`/`decide` reduction
that reaches it. A definition that is only ever *applied*, characterised by
lemmas, does not.

⛔ **Reduction is transitive and no grep sees it.** `rfl` and `decide` reduce
through the whole call graph, not just the names written in the statement.
`Codegen/Dispatch.lean:1600` pins `emitProgramR … := rfl`, which must reduce
`laHi` and the `GuestAddrs` constants — **neither appears in the statement**. So
a syntactic scan gives a lower bound on what must stay exposed, never the answer.
Decide per file, then let `lake build` be the oracle.

### What breaks, and what does not (all probed in this tree)

| mechanism, on a non-exposed `def` | result |
| --- | --- |
| `rfl` | ✗ `Note: … not exposed: probeDef ↦ 1` |
| `decide` | ✗ **but the message never says "exposed"** — see below |
| `simp only [f]` | ✗ `Invalid simp theorem …: Expected a definition with an exposed body` |
| `unfold f` / `delta f` | ✗ `Tactic 'unfold' failed to unfold` |
| `#guard` | ✅ **passes** — interpreter-checked, see §7b |
| `abbrev` (any tactic) | ✅ **passes — `abbrev` stays exposed regardless** |
| per-declaration `@[expose] def f` | ✅ works inside a plain `public section` |
| `#print axioms` / `axiomsweep` | ✅ clean — un-exposing adds no axiom taint |

Two of those are traps worth stating outright:

- ⚠️ **`decide`'s failure blames the wrong thing.** It reports *"its `Decidable`
  instance … did not reduce to `isTrue` or `isFalse` … reduction got stuck"* and
  never mentions exposure. Someone hitting it will go and audit their
  `Decidable` instance. If a `decide` breaks in a file whose exposure you just
  changed, suspect exposure first.
- ✅ **`abbrev` is auto-exposed.** Reading the toolchain suggests otherwise —
  there is no `reducible` carve-out at any `forceExpose` call site — but the
  probe is decisive: an `abbrev` under a plain `public section` still reduces by
  `rfl` and by `decide` from another module. So abbrev-dense files gain nothing
  from un-exposing, and offset tables such as `DivMod/Compose/Offsets.lean` and
  the generated `Codegen/RegionMapLinkPins.lean` are safe by construction.

### The predictor: count plain `def`s, ignore `abbrev`s

Because abbrevs stay exposed, the win tracks the number of plain `def`s and
nothing else. Measured:

| file | `def` | `abbrev` | public `.olean` |
| --- | ---: | ---: | ---: |
| `Stateless/SpecRef/IncrementalMptWrite.lean` | 50 | 0 | **−64 %** |
| `Evm64/Accelerators/Types.lean` | 1 | 31 | −0.3 % |
| `Evm64/EvmWordArith/Common.lean` (control) | 0 | 0 | **0, exactly** |

⇒ A file with no plain `def`s gains **nothing** — there is no body to withhold.
Un-exposing it is still worth doing for hygiene (it makes "unexposed" the
default, so a `def` added later is not silently exposed), but do not report it as
a build-time improvement.

#### ⚠️ …but `def` COUNT is only a proxy, and a bad one. Body SIZE is the win.

The three files above happen to vary in count and size together. They do not in
general, and the corrective case is stark:

| file | plain `def`s | public `.olean` |
| --- | ---: | ---: |
| `EL/Withdrawal.lean` | **1** | **−209 288 B (−71.9 %)** |
| `Stateless/VM/Precompiles.lean` | 141 (111 left unexposed) | −81 768 B (−12.2 %) |

`EL/Withdrawal.lean` is 100 lines holding one `structure` and one `def` —
`decodeWithdrawal`, an RLP decoder whose body elaborates to an enormous term. It
alone was **more than half** of its tranche's 408 KB, and 2.5x what
`Precompiles.lean` gave from 111 hidden definitions.

⇒ Rank candidates by the **size of the bodies you are withholding**, not by how
many there are. A single large decoder, interpreter step, or table-valued
definition outweighs a hundred small ones. Counting `def`s is a cheap first
filter — nothing more. (This also explains the `Evm64` leaf result below better
than its structural story alone: those files hold many *small* definitions.)

### ⚠️ Where the win is NOT: `Evm64` leaf opcodes

The `def`-count predictor tells you what a file *could* save. It does not tell
you whether the file will survive the build, and in `Evm64` those two pull in
opposite directions. Measured over one 82-file tranche across 15 leaf-opcode
directories (`Calldata`, `Shift`, `MLoad`, `MStore`, `Code`, `Env`, `Push`,
`Terminating`, `ReturnData`, `AddMod`, `Byte`, `And`, `Xor`, `Slt`, `Sgt`):

| | |
| --- | ---: |
| files un-exposed and still building | **10 of 82 (12 %)** |
| public `.olean` over those 10 | 704 672 → 677 208 B (**−3.9 %**) |
| share of the ~131 MB migrated public total | **0.02 %** |
| downstream modules freed from body-edit invalidation | 128 of 3045 (4.2 %) |
| full builds spent converging | 5 |

Two of the ten got **larger** (`Calldata/StageProgram` +240 B, `Env/Semantics`
+176 B): for a small body, the re-exported `.axiomInfo` costs more than the body
did. Un-exposing is not monotone in bytes.

**The mechanism, and why it generalises to the rest of `Evm64`.** Exposure mass
and cross-module value-reasoning are *correlated here*. The big definitions in
`Evm64` are big because they are RISC-V **programs** and **argument decoders**,
and those are exactly what downstream `unfold`s — `Calldata/CopySpec.lean:247`
does `unfold evm_calldatacopy` to split the program into preamble and loop. The
files that survived un-exposure are `*Spec`-shaped, whose public half is mostly
theorem *statements* — interface no matter what you do. So the files with
something to save are the ones that cannot save it.

⇒ Do **not** grind the remaining ~640 `Evm64` def-bearing files. Extrapolating
this tranche gives ~78 sticking files for ~210 KB, at ~40 full builds of
convergence. Spend the effort where large definitions are *not* value-reasoned —
`Stateless/SpecRef` is the demonstrated case (`IncrementalMptWrite.lean`, −64 %
on one file, more than 7× this entire tranche).

### Where the win IS: `Stateless/SpecRef`

The same loop, run over `Stateless/SpecRef`, gives the opposite answer — and the
contrast is the useful part, because the two tranches differ by 33x on a
directory a quarter the size:

| | Evm64 leaves | `Stateless/SpecRef` |
| --- | ---: | ---: |
| files un-exposed, still building | 10 of 82 | **13 of 37** |
| plain `def`s kept out of the interface | 40 | **268** |
| public `.olean` | 704 672 → 677 208 B (−3.9 %) | 1 475 448 → **575 696 B (−61.0 %)** |

Per file, the precompiles dominate: `PrecompilesBls` **−79.0 %**,
`PrecompilesBlsMap` −77.6 %, `PrecompilesHash` −75.2 %, `ElExecute` −75.3 %,
`Precompiles` −72.8 %, `PrecompilesCurve` −69.6 %, and `PrecompilesPairing`
−59.0 % on the largest single file (262 896 → 107 656 B).

**Why this directory and not that one.** `SpecRef` is the reference-implementation
layer; downstream *characterises* these definitions through correspondence
theorems rather than reducing through them, so the bodies leave the interface
cleanly. `Evm64`'s large definitions are RISC-V programs and argument decoders,
which is exactly what downstream `unfold`s. Same attribute, opposite outcome —
so **classify a directory by how downstream reasons about it, not by how many
`def`s it has.**

⇒ When picking the next tranche, ask which one it resembles.

### ⚠️ `Codegen` binds the ceiling from outside the batch

Excluding `Codegen` from a batch does **not** protect it: it *consumes* `SpecRef`,
and its `by decide` / `rfl` pins reduce transitively into these bodies.  Round 2
of the `SpecRef` tranche failed almost entirely inside `Codegen`
(`MemoryBudgetGuard`, `RequestsHashParams`,
`BlockVerdictTxStateGasArrayModel`) with `decide` failures and `maxRecDepth`,
and that alone forced back the five largest files in the directory —
`InstructionsCore` (118 `def`s), `Ssz` (85), `Transactions` (60),
`InstructionsEnv` (57), `Gas` (57): **377 `def`s**, well over the 268 that
survived.

So the remaining prize is not more un-exposing; it is those `Codegen` kernel
pins. Re-stating them so they do not reduce through `SpecRef` is a *semantic*
change to a kernel-checked proof, not a section-attribute edit — scope it as its
own piece of work, never as collateral inside an exposure PR.

### The surgical fallback: expose the declaration, not the file

When a failure **names** a definition — `Expected a definition with an exposed
body`, or ``unfold`` failed to unfold `f` — re-exposing the whole file
overpays. Put `@[expose]` on that one declaration inside the plain
`public section`, with the consumer named in a comment above it:

```lean
-- `@[expose]`: `SpecRef/HeaderRoundTrip.lean` unfolds this body.
@[expose]
def getNChecked (maxBytes : Option Nat) (b : Bytes) : Except SpecError Nat := …
```

Six such lines in `SpecRef/Stateless.lean` kept its other 18 `def`s out of the
interface (the file still measures **−41.7 %**), and one in
`Evm64/Calldata/CopyProgram.lean` saved that file. Note the asymmetry that makes
this worth trying: `decide`/`maxRecDepth` failures name nothing and reduce
through a whole closure, so they are the ones that genuinely cost a file.

### `EL` is bridge-shaped: expect it to wash out

Third tranche, 96 files across `Stateless/VM`, `Stateless/State`, `Crypto` and
`EL`. Ninety needed exposure; **six** survived, for −408 136 B (**−34.4 %**).
`EL` in particular washed out almost completely, and the shape is systematic:

* `*InputBridge` / `*ResultBridge` failed in round 2;
* `*EcallBridge` survived round 2 only to fail in round 3, once their consumers
  were rebuilt against the new interfaces;
* `EL/Conformance/*` failed throughout.

A bridge exists to be reduced through, so its bodies are interface by
construction. **Pre-filter `EL/*Bridge*.lean` out of a batch** rather than
spending a build round per wave rediscovering it. `Stateless/State/*Assertions`
also failed as expected — those are the `@[irreducible]` assertion bundles.

### The most actionable error message in this work

An in-file `rfl`/`decide` lemma that is *exported* forces its own file's
definitions to stay exposed, and Lean says so exactly:

```
Not a definitional equality: the left-hand side
  gasCost 0 0 0 0
is not definitionally equal to the right-hand side
  500
Note: This theorem is exported from the current module. This requires that all
definitions that need to be unfolded to prove this theorem must be exposed.
```

This names the culprit, so it is always worth the surgical treatment.
`Stateless/VM/Precompiles.lean` produced 21 of these; the LHS/RHS heads named
only **seven** distinct helpers (`bufferRead`, `emptyOutput`, `gasCost`,
`outputFromVerified`, `successOutput`, `successWordOutput`, `zeroWordOutput`),
recurring once per precompile namespace — 28 sites. Exposing those kept ~111 of
the file's 141 `def`s hidden.

⚠️ **Then the transitivity trap fires one round later.** `gasCost` was exposed
and `gasCost 0 0 0 0 = 500` *still* failed, because the reduction runs on
through `complexity` and `iterations`, which were not. Exposing a definition
does not expose what it calls — expect to chase the closure by one or two more
rounds, and read each round's LHS heads rather than assuming the first set was
complete.

### Relationship to `@[irreducible]`

`@[irreducible]` asks the elaborator not to unfold; *unexposed* means downstream
**cannot**, because the body is not in the interface. They point the same way, so
once a definition is unexposed its `@[irreducible]` is redundant — remove it in
the same commit.

### Measuring the pass

⛔ `scripts/import-graph-metrics.py` **cannot see this change.** It computes
cones from the import graph, which un-exposing does not touch, so
`sum_private_cone` reads identical before and after. Do not read that flatness as
failure. The meter is
`.github/workflows/scripts/oleansize_collect.sh`, which reports
`split_public_bytes` — the public half of modules that have a private half.

## 5a. `private` and `public` do not mix inside an exposed body

**A public declaration cannot reference a `private` one** once its body is
exposed, because the body *is* the interface. The headline error looks like an
ordinary typo — an `Unknown constant` or `Unknown identifier` pointing at a
helper defined a hundred lines above **in the same file**:

```
error: Unknown constant `EvmAsm.EL.RLP.RLPItem.decEq`      -- decEq is `private`
error: Unknown identifier `modexpReadLengthAsm`            -- and so is this
```

✅ **But Lean usually names the cause on the next line, and that note is the
right thing to grep for:**

```
Note: A private declaration `warmStorageKey` (from the current module) exists
but would need to be public to access here.
```

It appeared on 85 of wave EVM-1's errors and 40 of wave 10's. Keying a sweep on
the note rather than on `Unknown identifier` is strictly better: it distinguishes
this class from a genuine typo or a missing import, which the headline alone does
not. ⚠️ It is not universal, though — some sites give only the headline, so a
sweep should fall back to `Unknown identifier` and rely on the guards below.

⚠️ **The name in the error is not always the declaration.** Generalized field
notation reports the *whole dotted expression*, so a `private` table `s` used as
`s.getD j 0` surfaces as

```
error: Unknown identifier `s.getD`      -- the decl is `s`, NOT `getD`
```

which reads exactly like the qualified-constant shape `EvmAsm.Foo.bar` — where
the declaration is the **last** component — while pointing the opposite way. A
sweep that splits on the final dot silently finds nothing and reports "no
private references left", which is indistinguishable from being finished. EVM
wave 2 stalled twice on this (`s.getD`, then `sigma.getD`) inside a single file.
Try every component and prefer the one the file actually declares.

⚠️ **Knock-on errors in the same file are not separate problems.** An
unresolvable name leaves a hole in a term, so the elaborator then reports things
like `failed to synthesize instance of type class Decidable __do_lift✝` at an
unrelated line. Fix the private references and they disappear; do not chase them.

**The fix is to drop `private` from the referenced helper**, not to work around
it. That is the honest fix rather than merely the convenient one: if a public,
exposed definition's body mentions `f`, then any downstream proof that unfolds
that definition **already sees `f`**. The `private` was not buying encapsulation
for an exposed definition; removing it states what was already true.

⛔ `set_option backward.privateInPublic true` also makes it compile, and is
exactly what that option is for — but it emits a warning at every site
(*"Private declaration `X` accessed publicly; this is allowed only because the
`backward.privateInPublic` option is enabled"*), and this repo requires zero
warnings. Do not reach for it.

If you genuinely want the helper hidden, the answer is to stop exposing the
definition that references it — which is a Phase 4 narrowing decision, not
something to do in passing.

Scale, for planning: 762 files here carry `private` declarations (6806 in
total), and in wave 0, **3 of the 5 private-bearing files hit this**.

## 5b. Dropping `private` breaks `open private` at a distance

§5a's fix has a second-order consequence that the build reports **in a different
file**, sometimes hundreds of modules later: Batteries' `open private f from M`
resolves only names that are *actually* private in `M`. Make `f` public — which
is exactly what §5a tells you to do — and every `open private` naming it fails:

```
error: 'scalarItem' not found in the provided declarations:
  EvmAsm.Stateless.SpecRef.rlpTestHeader._closed_1
  EvmAsm.Stateless.SpecRef.rlpTestHeader✝
  ...
error: Unknown identifier `rlpTestHeader`
```

Two things make this hard to read. The list Lean prints is the *private*
declarations it did find, so the name you asked for is conspicuously absent
rather than reported as "no longer private". And the whole `open private`
command fails as a unit — so the **other** names on the same line come back as
`Unknown identifier` too, which is what the second error is. Do not chase that
one; fix the first and it goes away.

**The fix is to move the name off the `open private` line.** It is public now,
so a plain `open` reaches it:

```lean
-- before
open private scalarItem rlpTestHeader from EvmAsm.Stateless.SpecRef.BlocksRlp
-- after
open EvmAsm.Stateless.SpecRef (scalarItem)
open private rlpTestHeader from EvmAsm.Stateless.SpecRef.BlocksRlp
```

⚠️ **`open private` sites are not found by building the wave.** The consumer is
usually far downstream of the module whose `private` you dropped — in wave 6,
`BlocksRlp` is at level 6 and the five affected consumers are `Codegen/Programs`
files that a wave build never compiles. Grep instead, as part of the same fix:

```
$ grep -rn "open private" EvmAsm
```

and re-check every line that names a declaration you just widened. Five sites
here referenced `scalarItem`; one of them also carried an unrelated name on the
same line and reported it as a spurious second error.

### `open private` that SURVIVES still needs `import all`

The names you leave on the `open private` line have a second, independent
problem, and it does not appear until the *consumer* itself becomes a module. A
migrated module's private declarations live in a separate `.olean.private`, and
a plain or `public import` does not carry them:

```
error: Unknown constant
  `_private.EvmAsm.Stateless.SpecRef.BlocksRlp.0.EvmAsm.Stateless.SpecRef.rlpTestHeader`
```

⚠️ Read that mangled name carefully — it says Lean *knows* the declaration is
private in `BlocksRlp` and still cannot see it. This is not §5a (the name is
genuinely private, and correctly so) and not §5b's rename (there is nothing to
move off the line). It is a missing import **form**:

```lean
public import EvmAsm.Stateless.SpecRef.BlocksRlp
import all EvmAsm.Stateless.SpecRef.BlocksRlp   -- ← reaches the private half
```

Keep the existing `public import`; `import all` is an addition, not a
replacement. Both `EvmAsm/Stateless/SpecRef/HeaderRoundTrip.lean` and the
`Codegen/Programs/ValidateHeaderWhole*Witness.lean` files need this, and it is
the honest fix: a fixture like `rlpTestHeader` should stay private, and `import
all` is precisely the module system's way to say "I am reaching into this
module's private half on purpose."

## 5c. `private` changes the identity of COMPILER-GENERATED auxiliaries

§5a and §5b are about *referencing* a private declaration. This one is different
and much quieter: the private declaration is referenced only inside a proof, so
there is no visibility error at all — but the **auxiliary definitions Lean
generates for it** are private too, and therefore are *different constants* from
the ones generated for a public declaration.

A `match` inside a declaration produces a `…match_1` auxiliary; inside a
`private` declaration it produces `_private.….match_1`. Tactics that require
**syntactic** identity — `rw` above all — then fail to match across the boundary:

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  fromLimbs fun i => match i with
    | 0 => a.getLimbN 0
    ...
in the target expression
```

Observed in `Evm64/EvmWordArith/DivN4DoubleAddback.lean`, which carries a helper
whose entire purpose is to make the match-auxiliary identities agree —

> the auxiliary `match` function identity matches the one produced for our new
> lemmas' … patterns. Needed because `rewrite` requires syntactic identity of
> the match-auxiliary function, and Lean generates these per-file.

— and which was `private`, while the lemmas it was aligning with were public. The
two auxiliaries were the same constant before the migration and stopped being so
after. **Dropping `private` fixed it.**

⚠️ **What makes this hard to spot:** nothing reports a visibility problem. The
error names a rewrite pattern, points into unrelated-looking arithmetic, and the
declaration it blames is not the one that has to change. If a `rw` starts failing
in a migrated file on a pattern containing a `match`, `fun`, or a `where`
auxiliary, check whether either side is `private` **before** looking at the
mathematics.

⇒ **Rule of thumb: a helper that exists to align generated-definition identity
must have the SAME visibility as the declarations it is aligning with.**

## 5d. Duplicate declarations that `main` silently tolerates

The module system's import merge is **stricter than the old one**, and it
surfaces defects the migration did not create:

```
error: import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq failed,
  environment already contains
  'EvmAsm.Evm64.divK_mulsub_correction_addback_beq_v4_spec_within_noNop'
  from EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeqV4NoNop
```

Two modules declared the **same full name** — same statement, two different
tactic scripts, same namespace `EvmAsm.Evm64` — and both sit in `EvmAsm.Evm64`'s
import closure. That was true on `main`, where it built green. The migration is
only what made it visible.

⚠️ **Do not treat this as a conversion bug and do not paper over it.** Before
touching anything, establish which of the two the tree actually needs:

1. Diff the two declarations. If the *statements* match and only the proofs
   differ, it is an accidental duplication — the usual cause is two branches
   proving the same lemma and merging without conflict, since the two live in
   different files.
2. Check for an import cycle in **both** directions before collapsing them.
3. Keep the copy that sits with its thematic siblings, delete the other, and
   leave the emptied module as a `public import` re-export so its importers do
   not have to change. Say in the file why it is a shim.

Grepping for a duplicate by *name* finds this class; grepping by statement finds
the ones that have not collided yet.

## 6. Adding a new file

1. Write it with the header from §2 (or run the converter on it).
2. Register it in the corresponding umbrella module, as before — see AGENTS.md.
   The umbrella needs `public import`, or downstream consumers of the umbrella
   will not see your declarations.
3. `lake build`. If the file mixes ordinary definitions with metaprogramming, see
   §7.

**Downward-closure**: a `module` file cannot import a non-`module` file — the
same error for plain `import`, `public import`, `meta import`, and `import all`.
The reverse is fine. While migration is in flight this constrains where a new
file can sit; once it is complete, only the Sail boundary (§8) is affected.

## 7. The mixed metaprogramming/definitions trap

A file that mixes ordinary definitions with metaprogramming cannot be fixed by
any whole-file transform, and the converter will not try:

- Tagging the whole file `meta` makes its **data structures** meta too
  (*"PartialState.mk marked as meta"*).
- `private def … : MetaM` helpers stop being visible at an `elab` site **in the
  same file**.

These need per-**declaration** `meta`. Hand-fix them, and expect a cascade:
the build names one declaration at a time, and each one you mark pulls in the
next. `EvmAsm/Rv64/Tactics/SpecDb.lean` took seven, in this order:

```
getAllSpecs -> specGenExt -> the `initialize` block -> extractInstrCtorFromType
  -> findInstrCtorInCodeReq -> findInstrCtorInPre -> flattenSepConjPure
```

⚠️ **Modifier order is not free.** It is:

```lean
private meta partial def extractInstrCtorFromType ...
```

— visibility first, then `meta`, then `partial`/`noncomputable`/`unsafe`, then
the keyword. Both `meta private partial def` and `private partial meta def` are
**parse errors**, and the second one fails in a confusing way (it reports the
parse error *and* a `meta` diagnostic on the same line). Mathlib uses the same
order: 9 `private meta def`, 1 `private meta partial def`. If you are writing a new file and hit this, the usual
better answer is to split the metaprogramming into its own module — which is
what `*Attr.lean` files in this tree already do for simp attributes, and for the
same underlying reason.

## 7a. The `Rv64/Tactics` layer: migrate it by hand

Waves up to level 6 automate cleanly. **Level 7 and above pull in
`EvmAsm/Rv64/Tactics/*` (RunBlock, SeqFrame, XPerm, XPermPure, DropPure, XCancel),
where marking one elab entry point `meta` forces every declaration it reaches to
be `meta` too — a cascade the build reports ONE NAME AT A TIME.** Wave 10 needed
115 `meta` marks across five files, `RunBlock.lean` alone taking 29 rounds.

⚠️ **This section used to say the layer must be migrated by hand, one file per
PR. That is now too strong** — a loop that reads the build error, marks the one
name it names, and rebuilds does converge, and it is the only sane way to
service a 29-round cascade. What the loop needs is not manual driving but the
*guards* below. Automate it; do not automate it naively.

⛔ **The one hard stop that must remain a stop:** if the build exits **134**
(SIGABRT), do not iterate through it. See hazard 1.

Three hazards, each observed:

**1. ⛔ A tactic chain that is PARTLY `meta` SIGABRTs at its call sites.**

```
libc++abi: terminating due to uncaught exception of type lean::exception:
Could not find native implementation of external declaration
'EvmAsm.Rv64.Tactics.extractUnionChain'
```

`lean` **SIGABRTs (exit 134)**, and because the tactic is used everywhere the
failure fans out — errors across unrelated `Evm64/**` files that no reader would
connect to a `Rv64/Tactics` edit. The message suggests `supportInterpreter :=
true`; that is a red herring here.

⚠️ **This section previously said the cause was marking `extractUnionChain`
`meta`, and told you not to. That is wrong, and following it is what produces the
crash.** The cause is a **mix**: an interpreted (`meta`) caller reaching a
declaration that has no native implementation because *its* callees are `meta`.
`extractUnionChain` was a plain `partial def` calling into wave 10's `meta`
chain, so it could not be compiled and had no native symbol left to offer.

✅ **The fix was to mark `extractUnionChain` `meta` as well** — i.e. to make the
chain *consistent*, not to pull it back out. Verified directly: with that one
mark the failing `Evm64` modules build.

⇒ **The rule is: once an elab entry point is `meta`, everything it transitively
reaches must be `meta` too.** A partially-converted chain is the failure mode;
`meta` is not the hazard, the boundary is.

⚠️ **And the crash need not appear in the wave that causes it.** Wave 10 marked
115 declarations `meta` and built completely clean — because *the modules that
invoke those tactics were still unmigrated, so nothing exercised the boundary*.
The SIGABRT surfaced only in the next wave, when the callers became `module`
files. A green wave build is **not** evidence that its `meta` marks are safe;
this is the same structural blind spot that motivates `--check-tree-closure`.

**2. ⛔ Dropping `private` can create a duplicate declaration.** `getBvLitVal?`
is defined privately in **both** `Tactics/SeqFrame.lean` and
`Tactics/RunBlock.lean`, and the `private` is the only thing keeping them apart.
Dropping it yields ``a non-private declaration `…getBvLitVal?` has already been
declared``.

Two refinements, both learned by getting them wrong:

* ⛔ **Visibility is not the discriminator — the NAMESPACE is.** Every
  same-namespace sibling collides once one of them becomes public, whatever the
  sibling's own visibility:
  - a **public** sibling — `copyWordAsm`, private in `Programs/EIP7708Logs.lean`
    and already public in `Programs/EvmStackHandlers.lean`, both under
    `EvmAsm.Codegen`;
  - a **still-private** sibling — `fourTimes`, private in *both*
    `Proofs/ReloadHandler.lean` and `Proofs/HandlerSpecs.lean` under
    `EvmAsm.Codegen.Proofs`. Widening only one of them still gives
    ``a non-private declaration `EvmAsm.Codegen.Proofs.fourTimes` has already
    been declared``.

  ⚠️ It is tempting to reason that private names are mangled per module and so
  two privates cannot clash. **That reasoning is wrong** — I tried it and the
  build refuted it. Search for the name declared **at all** in the same
  namespace. `ReloadHandler.lean` even carried a comment asserting *"the two
  never collide — both are file-private"*, which is precisely the invariant
  widening destroys.
* ✅ **The clash is on the FULL name, so compare namespaces.** `plantedValidInput`
  is private in two files, but under `…Correspondence.Transaction` and
  `…Correspondence.Header` — different namespaces, no collision, widening is
  fine. Comparing bare names refuses safe work.

  ⚠️ **And "the namespace" means the stack open at the DECLARATION's line**, not
  the last `namespace` in the file. `millerSchedule` is private in
  `SpecRef/PrecompilesPairing.lean` under `…SpecRef.Bn128` and in
  `SpecRef/PrecompilesBls.lean` under `…SpecRef.Bls12` — no collision — but both
  files close with a trailing `namespace GasCosts … end GasCosts` block, so a
  last-line reading calls them equal and refuses a safe widening. Sibling
  namespace blocks in one file are common here; walk the `namespace`/`end` stack
  and stop at the declaration.

When two genuinely different functions do share a name in one namespace, the fix
is to **rename** the one that must become public, not to abandon the widening.

**3. Try `meta` FIRST; widen visibility only if that made no progress.**
SeqFrame's `getBvLitVal?` needed only `meta` — dropping its `private` in the
same pass caused hazard 2 for nothing. `private meta def` is a valid and often
correct combination.

### The seven error shapes

A fixer that knows only the first one stalls on the rest. Wave 10 met all seven:

| message | what to do |
| --- | --- |
| ``Invalid `meta` definition `f`, `g` not marked `meta`` | mark `g` |
| ``Invalid definition `f`, may not access `g` marked as `meta`` | mark **`f`** — the *container*; this one **inverts** |
| ``Cannot add attribute [tacticElabAttribute]: Declaration `f` must be marked as `meta`` | mark `f` |
| a `where`-auxiliary, surfacing as `parent.aux` | mark the **parent** |
| ``failed to compile definition, consider marking it as 'noncomputable' because it depends on 'g', which is 'noncomputable'`` | mark the **caller** — the declaration on the reported line. ⛔ Do **not** take the message's advice: `noncomputable` is the wrong fix; the caller belongs in the meta layer |
| ``Unknown identifier `g`` where `g` **is** already `meta` | mark the **containing definition** — a non-`meta` body cannot see a `meta` name, and it says "unknown", not "may not access" |
| ``Unknown attribute `[my_attr]`` | not a `meta` mark at all — the file **applies** an attribute and needs a `meta import` of the module declaring it |

### Three traps in the fixer itself, not in Lean

* ⛔ **Modifier order is `private meta partial def`.** Inserting `meta`
  immediately before `def` gives `private partial meta def`, which is a parse
  error (``unexpected token 'meta'``). `meta` goes after the visibility modifier
  and *before* `partial`/`noncomputable`.
* ⛔ **An identifier ending in `?` breaks a shell locator.** In ERE, the `?` in
  `getAddrOffset?` is a **quantifier**, so `grep -E "def getAddrOffset?"` matches
  the wrong thing and reports the declaration as missing. Locate in a language
  where you can escape the name.
* ⛔ **The reported name may be namespace-qualified.** `OwnershipKind.key` is
  written `private def OwnershipKind.key`, so stripping to the bare `key` finds
  nothing. Try the dotted name first, then the bare one.

## 7b. When a proof needs to unfold an UPSTREAM definition

`@[expose]` covers your own declarations. It does nothing for imported ones, and
**nothing reaches a non-exposed imported body** — `import all`,
`with_unfolding_all rfl` and `decide` were all tried and all fail, because Lean
represents such definitions as unfold *axioms*, not as bodies it is declining to
unfold. The symptom is a note on a type mismatch:

```
Note: The following definitions were not unfolded because their definition is
not exposed:
  String.intercalate ↦ 3
```

Confirmed minimally: in a migrated file `"a" ++ "b" = "ab" := rfl` succeeds and a
locally-defined exposed `intercalate` reduces fine; only core's fails.

**Two core definitions this repo trips over are `String.intercalate` and
`Nat.repr`.** The second is the wider problem: `Nat.repr` backs `toString` on
`Nat`, so *any* kernel-checked `rfl` that renders a number into a string breaks.

```lean
example : "a" ++ "b" = "ab" := rfl          -- OK
example : toString (5 : Nat) = "5" := rfl   -- FAILS: `Nat.repr` not exposed
example : s!"x{(5 : Nat)}" = "x5" := rfl    -- FAILS, same cause
```

For a repo that emits assembly text and pins it with `rfl`, that is a real cost,
not a curiosity — it is what made `EvmAsm/Codegen/Emit.lean` the migration's
most expensive blocker, holding back a reverse cone of 1037 modules until it
owned its own renderers.

### ⚠️ The note is incomplete by construction — and worse than that in practice

`mkUnfoldAxiomsNote` lists only constants whose original kind is `.defn`, so a
blocked `opaque` or `@[extern]` definition is **silently omitted**. But the
sharper observation, measured on Emit, is about *where* the note appears:

| | note said |
| --- | --- |
| the real failing example | `String.intercalate` only — `Nat.repr` absent |
| after fixing `String.intercalate` | **nothing at all** |
| a one-line probe in the same file | `Nat.repr ↦ 3`, immediately |

⇒ **A minimal probe is strictly more informative than the actual failure site,
and an absent note is not evidence that exposure is fine.** Write the smallest
`example : f x = <literal> := rfl` you can and check *that*; do not reason from
what the composite error reported.

### The fix: own an exposed copy of what you compute through

Two traps, both of which trade one blocker for another:

- ⛔ **Well-founded recursion does not reduce by `rfl` either.** A `decreasing_by`
  definition fails exactly like a non-exposed one. Recurse structurally — on a
  fuel argument if the natural measure is not structural.
- ⛔ **Do not route through `Char`/`UInt32` to build digits.** `Char.ofNat (48 + d)`
  re-enters core definitions whose exposure you then have to verify too. Match on
  a `Nat` literal and return a one-character string literal.

Reduction that stays inside `Nat` literal arithmetic and `String` literal append
is reliable: the kernel does `Nat` on GMP integers, and `"a" ++ "b" = "ab" := rfl`
holds.

### Replacing a core function is a semantic change — check parity against it

If the definition you now own feeds a **code generator** or anything else whose
output is compared byte-for-byte elsewhere, prove the replacement agrees:

```lean
#guard (List.range 1000).all (fun n => natStr n == toString n)
#guard joinLines ["a","","c"] == String.intercalate "\n" ["a","","c"]
```

⭐ State these as `ours == core`, **never as pinned literals** — a pinned literal
still passes if both sides drift together, which makes it a tautology rather than
a parity check.

⚠️ This does **not** license replacing a kernel-checked `rfl` with a `#guard`.
`#guard` is interpreter-checked and strictly weaker; it is an *additional*
obligation on the new definition, sitting alongside the `rfl` examples that were
the reason to own the definition in the first place. If you find yourself
downgrading an `example … := rfl` to a `#guard` to make something pass, you have
recorded the bug rather than fixed it.

## 8. The Sail boundary

`EvmAsm/Rv64/SailEquiv/StateRel.lean` does `import Out`, the vendored
Sail-extracted model, which is not migrated (0 of 116 files) and whose own
dependency — the upstream `Sail` runtime — is not ours to migrate. By
downward-closure that blocks exactly **24 modules**: the 22 SailEquiv leaves,
`StateRel` itself, plus `EvmAsm/Rv64.lean` and `EvmAsm.lean`.

This is accepted, not a bug. Invalidation stops at a migrated module whose
interface is unchanged, so an unmigrated straggler only rebuilds when something
it *directly* imports changes. Do not try to work around it by de-migrating
anything else.

## 9. Reading the metrics in a PR

Wave 0 (68 leaf modules, 2.2 % of the tree) insulated **4.9 % of the tree's
total invalidation mass**, because the leaves are also the deepest hubs:
`Rv64.Word` went from `cone 2873` to `private_cone 1`. Expect later waves to
give less per file.

`python3 scripts/import-graph-metrics.py --check` gates two things and reports a
third:

- **`module_headers`** — a monotone floor. It may only rise. A drop means a
  `module` header was removed and a module rejoined the invalidate-everything
  regime.
- **`outside` / `slack` / `bytes_outside`** — the growth-proof complements of the
  cone metrics, as before. See that script's header for why the complement and
  not the raw count.
- **`redundant_edges`** — advisory, never ratcheted. Ordinary growth can raise it
  legitimately (a new file importing both a hub and one of the hub's own
  dependencies), so gating it would reproduce the #12789 defect. It is the
  progress meter for the narrowing pass in §3, and nothing else.

`--private-cone` shows the conservative cone beside the interface-invalidation
cone. Read them as the two halves of the edit distribution, **not** as
before/after: `private_cone` is the cost of an interface-preserving edit, and an
interface-changing edit still pays the full `cone`.
