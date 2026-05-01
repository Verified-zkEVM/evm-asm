# #1075 spurious-parens audit (slice 1)

Audit of remaining spurious single-symbol parentheses across `EvmAsm/`,
classifying findings into:

- (a) **safe-to-strip** in expressions
- (b) **intentional** (precedence in tactic blocks, ascription, polymorphic
  literals where parens disambiguate)
- (c) **inside string/doc comments** — out of scope

No code changes in this slice. Slice 2 (`evm-asm-y7uu`) will land the first
cleanup PR for category (a). All counts below are `lake build` green at
`origin/main`.

## Methodology

`rg -P` regex sweep across `EvmAsm/`, then manual filter for code-only
matches (drop lines starting with `--` or inside `/-- ... -/`). Patterns
that returned zero code matches are noted as "exhausted" — the parent
sweep tracked at `evm-asm-d2p0` has already drained them via PRs
#1144 / #1424 / #1425 / #1426 / #1475 / #1478.

## Patterns surveyed

| Pattern | Code matches | Disposition |
|---|---|---|
| `apply\|exact\|refine \(ident\)` (sole-arg paren) | 0 | (exhausted) |
| `[\(ident\),`/`[\(ident\)]` simp-list paren | 0 | (exhausted) |
| `at \(ident\)` | 0 | (exhausted) |
| `:= \(ident\)$` | 0 | (exhausted) |
| `from \(ident\)` | 0 | (exhausted) |
| `← \(ident\)` rewrite | 0 | (exhausted) |
| `, \(ident\) [,⟩\]]` (list/tuple) | 0 | (exhausted) |
| `⟨\(ident\),` anon constructor | 0 | (exhausted) |
| `\(QualifiedName\).proj` (paren-then-projection) | **21** | **(a) safe-to-strip** |
| `\([0-9]+\)` paren-around-numeric-literal | ~111 (mostly comments / `O(1)` / `(0)` after `<<<` shift index where ascription matters) | (b) intentional / (c) comment |
| `\(ident\)` standalone EOL | ~179 raw, dominated by comments / closure parens | (c) comment-heavy — defer |

## Category (a) — safe-to-strip findings

Pattern: `(QualifiedName).proj` where `QualifiedName` is a single
fully-qualified identifier (no internal whitespace, operators, or
arguments) and `.proj` is one of `mp`, `mpr`, `symm`, `left`, `right`,
`elim`, `out`, `trans`. Field-projection precedence is higher than
juxtaposition, so the parens are redundant; dropping them does not change
parse. All 21 lines below were verified to fit this shape.

```
EvmAsm/Evm64/EvmWordArith/MaxTrialVacuity.lean:190:  exact (EvmWord.ult_iff).mpr h_lt
EvmAsm/Evm64/EvmWordArith/KnuthTheoremB.lean:342:  exact (EvmWord.ult_iff).mp h
EvmAsm/Evm64/EvmWordArith/KnuthTheoremB.lean:851:    (EvmWord.ult_iff).mp h_check
EvmAsm/Evm64/DivMod/LoopDefs/IterV4InvariantsHelpers.lean:383:    rcases (Nat.div_eq_zero_iff).mp h_div_zero with h | h
EvmAsm/Evm64/DivMod/LoopDefs/IterV4InvariantsHelpers.lean:618:    rcases (Nat.div_eq_zero_iff).mp h_div_zero with h | h
EvmAsm/Evm64/DivMod/SpecCallShift0.lean:80:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/SpecCallShift0.lean:245:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/SpecCallShift0.lean:434:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Shift0AddbackMod.lean:173:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Shift0AddbackMod.lean:280:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/Base.lean:755:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/Base.lean:854:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/Base.lean:1037:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:264:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:340:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:426:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:509:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:605:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:678:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:775:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
EvmAsm/Evm64/DivMod/Spec/CallSkip.lean:846:    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
```

Recommended slice-2 PR: rewrite all 21 occurrences as
`QualifiedName.proj args` (drop only the outer parens; preserve everything
else). Diff is purely whitespace + 2 chars per line × 21 lines, ≤ 30 fixes
cap from the slice-2 description. `lake build` green expected with no
proof body changes.

## Category (b) — intentional (do NOT touch)

- `\(0\)` / `\(1\)` after `<<<`, `>>>`, `^` — the parens often act as type
  hints for polymorphic literal disambiguation in `BitVec`/`Word` shift
  expressions (e.g. `(1 : Word) <<< (3 : BitVec 6).toNat`). Some "bare"
  numeric-paren matches are subtly load-bearing here; do not bulk-strip.
- `O(1)`, `O(n)` etc. inside doc comments — out of scope.
- `Tactics/SeqFrame.lean` macro `$(...)` antiquotation parens — required
  by the macro-elaborator grammar.
- Type-ascription parens like `(x : Foo)` — single-symbol body, but parens
  are required to attach the ascription.

## Category (c) — inside string / doc comments

Skipped entirely. The bulk of the remaining `\([0-9]+\)` and trailing
`\(ident\)` matches live in `/-- ... -/` doc comments (register banks,
ABI tables, RLP-phase comments) where the parens are part of human-prose
formatting (e.g. `x10 (a0)`, `selfBalance (EvmWord)`, `(reserved)`).
Stripping these has no semantic effect but also no semantic gain, and
risks reflowing tables. Out of scope for this sweep.

## Status

Parent sweep `evm-asm-d2p0` (#1075) has already drained patterns A–H via
the merged batches above. This audit identifies one remaining safe
category — paren-then-projection — with **21 occurrences** ready for
slice-2 cleanup. No further audit slices needed unless a new spurious
pattern appears in future refactorings.
