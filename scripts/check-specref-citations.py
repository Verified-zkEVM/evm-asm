#!/usr/bin/env python3
"""check-specref-citations.py — ADVISORY architecture fitness function (GH #11517).

Validates `<Module>.lean:<line>` citations of `SpecRef` modules in the kernel-checked
correspondence registry: the cited line must actually be near the cited symbol.

Why
---
`EvmAsm/Progress/Correspondence.lean` grades each audited routine against a `SpecRef`
counterpart and names it with a `file:line`. **Nothing checked those line numbers** —
`scripts/check-spec-refs.sh` validates *Python* (`execution-specs`) citations only — so
they rot silently as SpecRef modules grow. Two had drifted into unrelated code:

  * `_decode_header` cited at `SpecRef/Stateless.lean:158` (two rows). Actual `:210`;
    line 158 is `| .ok _ => true` inside an unrelated private helper.
  * `logs_bloom` cited at `Fork.lean:101`. Actual `:128`; line 101 is a deposit-log
    pubkey-offset check.

Plus two harmless off-by-ones onto the docstring above the `def`
(`PrecompilesBls.lean:78` → `:79`, `PrecompilesCurve.lean:83` → `:85`).

A verdict is only as good as the counterpart it names. A citation pointing at
unrelated code invites the next reader to grade against the wrong function — worse
than no citation, because they would go looking.

What it checks
--------------
For every `` `symbol` `` followed (within a short span) by `<Module>.lean:<N>`, where
`<Module>.lean` resolves under `EvmAsm/Stateless/SpecRef/`, the symbol must appear
within ±WINDOW lines of N. The window tolerates citing a docstring just above its
`def` while still catching a citation that has drifted to unrelated code.

Deliberately advisory: SpecRef modules get renamed and reorganised, and this should
nudge rather than block. `--strict` exits non-zero for a PR-time gate if wanted.

Usage:
  scripts/check-specref-citations.py             # advisory (always exit 0)
  scripts/check-specref-citations.py --strict    # exit 1 on drift
  scripts/check-specref-citations.py --self-test
"""

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
REG = REPO / "EvmAsm" / "Progress" / "Correspondence.lean"
SPECREF = REPO / "EvmAsm" / "Stateless" / "SpecRef"
WINDOW = 4

# A backticked symbol, then up to 80 chars of prose (no intervening backtick, so the
# symbol is the NEAREST one), then `Module.lean:123`.
CITE_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.]*)`[^`]{0,80}?([A-Za-z][A-Za-z0-9]*)\.lean:(\d+)")

DEF_RE = "(?:def|theorem|abbrev|structure|inductive)"


def citations(text: str):
    """Yield (symbol, module, line) for citations naming a real SpecRef module."""
    for m in CITE_RE.finditer(text):
        sym, mod, line = m.group(1), m.group(2), int(m.group(3))
        if (SPECREF / f"{mod}.lean").is_file():
            yield sym, mod, line


def decl_span(lines: list[str], bare: str) -> tuple[int, int] | None:
    """1-based [start, end) span of the declaration named `bare`: its own line through
    the line before the next top-level declaration.

    ⚠️ The span, not a fixed window, is the right rule — and the gate's own first run
    proved it. `validate_header` is cited at `SeamShell.lean:248` while being defined
    at `:232`, because the citation names the enclosing function and points at the
    CLAUSE inside it (`extraData.length > 32`). That is a legitimate and deliberate
    pattern here: the crypto rows audit individual clauses rather than whole
    functions. A ±4 window rejected it as drift. Accepting anything inside the
    definition's body keeps clause-level citations while still catching a citation
    that has landed in a different function entirely.
    """
    start = None
    for i, ln in enumerate(lines, start=1):
        if re.match(rf"^\s*{DEF_RE}\s+{re.escape(bare)}\b", ln):
            start = i
            break
    if start is None:
        return None
    end = len(lines) + 1
    for i in range(start + 1, len(lines) + 1):
        if re.match(rf"^{DEF_RE}\s+\w", lines[i - 1]):
            end = i
            break
    return start, end


def check(text: str) -> tuple[int, list[str]]:
    checked, problems = 0, []
    for sym, mod, line in citations(text):
        path = SPECREF / f"{mod}.lean"
        lines = path.read_text().splitlines()
        checked += 1
        if line > len(lines):
            problems.append(
                f"  ✗ {sym}  {mod}.lean:{line} — beyond end of file ({len(lines)} lines)")
            continue
        bare = sym.split(".")[-1]
        span = decl_span(lines, bare)
        if span is not None:
            start, end = span
            # Accept the docstring immediately above the `def` too.
            if start - WINDOW <= line < end:
                continue
            problems.append(
                f"  ✗ {sym}  {mod}.lean:{line} — outside its definition "
                f"(body spans {start}..{end - 1})")
            continue
        # No declaration by that name: fall back to a proximity check, since the
        # citation may name a field, a constructor, or Python-side prose.
        lo, hi = max(0, line - 1 - WINDOW), min(len(lines), line + WINDOW)
        if sym not in "\n".join(lines[lo:hi]) and bare not in "\n".join(lines[lo:hi]):
            problems.append(
                f"  ✗ {sym}  {mod}.lean:{line} — no such declaration, and symbol "
                f"not within ±{WINDOW} lines")
    return checked, problems


def self_test() -> int:
    """A gate nobody has seen fail is indistinguishable from one that cannot fail —
    and catching a wrong-line citation is this gate's entire purpose."""
    failures = []

    # `_decode_header` really is in Stateless.lean, but not at line 1.
    planted = 'reference := "the `_decode_header` port (SpecRef/Stateless.lean:1)"'
    checked, problems = check(planted)
    if checked != 1:
        failures.append(f"planted citation not extracted (checked={checked})")
    elif not problems:
        failures.append("planted wrong-line citation was NOT flagged")

    # A correct citation must NOT be flagged.
    real = re.search(r"^\s*def\s+_decode_header\b",
                     (SPECREF / "Stateless.lean").read_text(), re.M)
    if real:
        n = (SPECREF / "Stateless.lean").read_text()[:real.start()].count("\n") + 1
        ok = f'reference := "the `_decode_header` port (SpecRef/Stateless.lean:{n})"'
        c2, p2 = check(ok)
        if c2 != 1:
            failures.append(f"correct citation not extracted (checked={c2})")
        elif p2:
            failures.append(f"correct citation falsely flagged: {p2}")

    # A non-SpecRef module must be ignored rather than reported missing.
    c3, _ = check('`foo` (Codegen/Programs/Whatever.lean:12)')
    if c3 != 0:
        failures.append("non-SpecRef citation was not ignored")

    if failures:
        print("check-specref-citations --self-test: FAIL", file=sys.stderr)
        for f in failures:
            print(f"    {f}", file=sys.stderr)
        return 1
    print("check-specref-citations --self-test: OK — wrong-line citation caught, "
          "correct one accepted, non-SpecRef ignored.")
    return 0


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    if not REG.is_file():
        print(f"check-specref-citations: {REG} not found — skipping.", file=sys.stderr)
        return 0
    checked, problems = check(REG.read_text())
    for p in problems:
        print(p)
    print(f"check-specref-citations: {checked} SpecRef citation(s) checked, "
          f"{len(problems)} drifted.")
    if problems:
        print("\nA `reference` naming the wrong line sends the next reader to unrelated\n"
              "code and invites grading a verdict against the wrong function. Update the\n"
              "line number in EvmAsm/Progress/Correspondence.lean.", file=sys.stderr)
        if "--strict" in sys.argv[1:]:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
