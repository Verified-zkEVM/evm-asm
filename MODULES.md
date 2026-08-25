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

`@[expose] public section` at the top of every file preserves today's behaviour:
downstream proofs can see through definitions exactly as they can now. This tree
depends on that heavily — roughly 1200 `@[irreducible]`, 8400 `unfold`, and
13000 `simp only [<def>]` sites.

**Do not remove `@[expose]` from a file in an ordinary PR.** It is a semantic
change: an unexposed definition cannot be unfolded downstream, and proofs that
relied on defeq will break. Tightening it is a deliberate, measured, later pass.

When that pass runs, the rule of thumb will be:

- A definition whose *value* downstream proofs reason about (`simp [f]`,
  `unfold f`, `decide` on a concrete instance, `rfl`) needs `@[expose]`.
- A definition that is only ever *applied*, with its behaviour characterised by
  lemmas, does not — and is better off unexposed, because then changing its body
  does not invalidate the cone.

Note the relationship to `@[irreducible]`, which this repo already uses to say
"do not unfold this". `@[irreducible]` asks the elaborator not to unfold;
*unexposed* means downstream cannot unfold it at all, because the body is not in
the interface. They point the same way, and once a definition is unexposed its
`@[irreducible]` is usually redundant.

## 5a. `private` and `public` do not mix inside an exposed body

**A public declaration cannot reference a `private` one** once its body is
exposed, because the body *is* the interface. The symptom is misleading — an
`Unknown constant` or `Unknown identifier` pointing at a helper defined a
hundred lines above **in the same file**:

```
error: Unknown constant `EvmAsm.EL.RLP.RLPItem.decEq`      -- decEq is `private`
error: Unknown identifier `modexpReadLengthAsm`            -- and so is this
```

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
`EvmAsm/Rv64/Tactics/*` (RunBlock, SeqFrame, XPerm, XPermPure, DropPure), and
those must be migrated by hand, one file per PR.** A batch fixer driven by build
errors gets them wrong in three ways, each of which was observed:

**1. ⛔ Marking `meta` on a declaration a COMPILED tactic uses at runtime is
catastrophic, not a no-op.** Marking `SeqFrame.extractUnionChain` meta gives:

```
libc++abi: terminating due to uncaught exception of type lean::exception:
Could not find native implementation of external declaration
'EvmAsm.Rv64.Tactics.extractUnionChain'
```

`lean` **SIGABRTs (exit 134)**, and because the tactic is used everywhere the
failure fans out — 115 errors across unrelated `Evm64/**` files that no reader
would connect to a Tactics edit. The message suggests `supportInterpreter :=
true`; that is a red herring here.

**2. ⛔ Dropping `private` can create a duplicate declaration.** `getBvLitVal?`
is defined privately in **both** `Tactics/SeqFrame.lean` and
`Tactics/RunBlock.lean`, and the `private` is the only thing keeping them apart.
Dropping it yields ``a non-private declaration `…getBvLitVal?` has already been
declared``. Before dropping a `private`, check the name is not declared
non-privately elsewhere.

**3. Try `meta` FIRST; widen visibility only if that made no progress.**
SeqFrame's `getBvLitVal?` needed only `meta` — dropping its `private` in the
same pass caused hazard 2 for nothing. `private meta def` is a valid and often
correct combination.

### The four error shapes

A fixer that knows only the first one stalls on the rest:

| message | what to mark `meta` |
| --- | --- |
| ``Invalid `meta` definition `f`, `g` not marked `meta`` | `g` |
| ``Invalid definition `f`, may not access `g` marked as `meta`` | **`f`** — the *container* |
| ``Cannot add attribute [tacticElabAttribute]: Declaration `f` must be marked as `meta`` | `f` |
| a `where`-auxiliary, surfacing as `parent.aux` | the **parent** |

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
not a curiosity — it is why `EvmAsm/Codegen/Emit.lean` is deferred.

⚠️ **The "not exposed" note is incomplete by construction.** `mkUnfoldAxiomsNote`
only lists constants whose original kind is `.defn`, so a blocked `opaque` or
`@[extern]` definition is silently omitted. Never read an absent note as
"exposure is not the problem" — probe it minimally instead. That mistake cost a
round of blind debugging here.

**The fix is to own an exposed copy of whatever you compute through**, with the
same equations. Do not reach for `#guard` — that trades a kernel-checked
assertion for an interpreter-checked one, which is a real weakening in this
repo, not a formatting choice.

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
