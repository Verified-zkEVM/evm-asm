# 1075 spurious-parens audit (slice 1)

GH issue: [#1075](https://github.com/Verified-zkEVM/evm-asm/issues/1075).

This is the audit slice for [`evm-asm-wxaj`](https://github.com/Verified-zkEVM/evm-asm/issues/1075):
classify single-symbol parenthesizations across `EvmAsm/` so the cleanup
slice (`evm-asm-y7uu`) only touches the safe-to-strip ones.

## Method

Regex sweep over all `.lean` under `EvmAsm/` (390 files) for two patterns,
after stripping `/- ... -/`, `--`, and `"..."` (so hits inside doc comments
or string literals are excluded):

  - `\(([A-Za-z_][A-Za-z0-9_']*)\)` — paren around a bare identifier
  - `\(([0-9]+)\)`                 — paren around a bare numeric literal

A line is then classified as *intentional* (paren is required syntax) when
it begins with one of: `open`, `export`, `namespace`, `attribute`,
`notation`, `infixl/r`, `prefix`, `postfix`, `syntax`, `macro`, `elab`,
`initialize`, `instance`, `abbrev`, `deriving`, `protected`, `private`.

Script: ad-hoc Python under `/tmp/parens_audit.json` (not committed).

Counts (as of `origin/main` at this audit):

| pattern   | total | safe-candidates | intentional/syntax |
|-----------|-------|-----------------|---------------------|
| `(ident)` |   64  |        5        |         59          |
| `(num)`   |    9  |        9        |          0          |

## Bucket A — safe-to-strip (9 hits, 4 files)

All numeric: `cpsTripleWithin (21)` / `cpsTripleWithin (8)` where the
parenthesized literal is just a function argument and reads identically
without the parens. Removing them is a pure whitespace change.

```
EvmAsm/Evm64/DivMod/Compose/ModPhaseBn3.lean:25      (21)
EvmAsm/Evm64/DivMod/Compose/PhaseAB.lean:214         (8)
EvmAsm/Evm64/DivMod/Compose/PhaseAB.lean:253         (21)
EvmAsm/Evm64/DivMod/Compose/PhaseAB.lean:491         (21)
EvmAsm/Evm64/DivMod/Compose/PhaseAB.lean:626         (21)
EvmAsm/Evm64/DivMod/Compose/PhaseAB.lean:796         (21)
EvmAsm/Evm64/DivMod/Compose/ModPhaseB.lean:119       (21)
EvmAsm/Evm64/DivMod/Compose/ModPhaseBn21.lean:26     (21)
EvmAsm/Evm64/DivMod/Compose/ModPhaseBn21.lean:197    (21)
```

These are the targets for slice 2 (`evm-asm-y7uu`).

## Bucket B — intentional / risky (64 hits)

### B1. `open Foo (name)` — required syntax (59 hits)

`open` with an explicit identifier list uses `( ... )` as part of the
declaration grammar. Removing the parens is a syntax error. Examples:

```
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1)
```

These were flagged because the contents are a single identifier; they
should NOT be touched.

### B2. Macro antiquotation `$(ident)` (5 hits)

In `EvmAsm/Rv64/Tactics/SeqFrame.lean` and `RunBlock.lean`, the form
`$(n1Stx)` / `$(s)` appears inside `Tactic`/`MetaM` quotation blocks.
Although `$x` and `$(x)` parse equivalently for a bare ident inside a
splice, conservatively leave these alone — the parenthesized form
generalizes to compound spliced terms and the surrounding code mixes
both forms intentionally.

```
EvmAsm/Rv64/Tactics/SeqFrame.lean:322   $(n1Stx)  $(n2Stx)
EvmAsm/Rv64/Tactics/SeqFrame.lean:375   $(n2Stx)
EvmAsm/Rv64/Tactics/SeqFrame.lean:395   $(n1Stx)
EvmAsm/Rv64/Tactics/RunBlock.lean:872   $(s)
```

## Bucket C — out of scope

  - paren-with-type-ascription, e.g. `(0 : Word)`, `(x : Nat)` — not
    captured by the regex (the `:` blocks the match).
  - parenthesized binders in `def f (x : Nat)` / `theorem foo (h : P)` —
    required syntax.
  - parens inside `/- ... -/` and `--` comments — stripped before scan.

## Recommendation

Slice 2 (`evm-asm-y7uu`, ~30-fix cap) is well within budget: only 9 fixes
are needed across 4 files, all of them removing parens around a literal
`21` or `8` passed to `cpsTripleWithin`. After slice 2 the audit is
empty and the parent (`evm-asm-d2p0` / GH #1075) can be closed.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
