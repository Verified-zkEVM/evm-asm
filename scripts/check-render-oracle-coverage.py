#!/usr/bin/env python3
"""Check that every guarded standalone render has an external oracle.

``*_eq_prog`` is a useful kernel-checked tie, but it renders a Program back to
the same string used to define the Function.  It therefore cannot detect a
drift that is shared by both sides.  This gate keeps that self-tie from being
the only evidence for a standalone emitted routine: each direct
``"entry:\\n" ++ emitProgram(R)? ...`` render must have either

* a ``GuestImageEntries`` row keyed by the emitted *entry symbol*; or
* an ``asm-fixtures/<Function>.s`` fixture.

The two names are deliberately different.  GuestImageEntries is keyed by the
snake-case linker symbol (``GuestAddrs.foo_bar``), while fixtures are keyed by
the Lean Function name (``fooBarFunction.s``).  Matching one convention on the
other would report a false green (the failure that motivated #12829).

The scan intentionally excludes concatenation factors.  A theorem such as
``dispatchLoopLabeledFunction_eq_prog`` has an extra string after the render,
and an exported ``.globl`` wrapper has text before the entry label; neither is
a standalone render whose bytes this gate can oracle.  The discovery floor is
separate from the coverage check: if the parser ever stops seeing the source
population, the gate fails instead of printing a reassuring zero.

Usage::

    python3 scripts/check-render-oracle-coverage.py
    python3 scripts/check-render-oracle-coverage.py --self-test
"""

from __future__ import annotations

import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE_ROOT = REPO / "EvmAsm" / "Codegen"
ENTRIES = REPO / "EvmAsm" / "Codegen" / "Proofs" / "GuestImageEntries.lean"
FIXTURES = REPO / "scripts" / "asm-fixtures"

# Measured on origin/main a1dcd2d36.  This is a lower bound rather than an
# exact equality: adding a guarded pair is harmless, while a drop requires an
# explicit review of the source population and an intentional floor update.
EXPECTED_GUARDED_PAIRS_FLOOR = 570

THEOREM_START = re.compile(
    r"(?m)^\s*theorem\s+(?P<function>[A-Za-z_][A-Za-z0-9_]*Function)_eq_prog\b"
)
FUNCTION_DEF = re.compile(
    r"(?m)^\s*def\s+(?P<function>[A-Za-z_][A-Za-z0-9_]*Function)\s*:\s*String\s*:="
)


@dataclass(frozen=True)
class RenderPair:
    function: str
    entry: str
    program: str
    source: Path


def _theorem_region(text: str, start: int) -> str | None:
    """Return one theorem's type through ``:= rfl``.

    All generated render ties in this tree are declarationally proved by rfl.
    Stopping at that token keeps comments and the next declaration out of the
    parse, while still accepting the multiline formatting used by the source.
    """

    match = re.search(r":=\s*rfl\b", text[start:])
    if match is None:
        return None
    return text[start : start + match.end()]


def _decode_string(raw: str) -> str:
    """Decode the tiny Lean string literal subset used for entry labels."""

    # Entry prefixes contain only the label and ``\\n``.  Avoid a broad
    # unicode-escape decoder so malformed source fails the shape test rather
    # than being silently normalised into a different name.
    out: list[str] = []
    i = 0
    while i < len(raw):
        if raw[i] != "\\":
            out.append(raw[i])
            i += 1
            continue
        if i + 1 >= len(raw):
            return ""
        esc = raw[i + 1]
        if esc == "n":
            out.append("\n")
        elif esc == "\\":
            out.append("\\")
        elif esc == '"':
            out.append('"')
        else:
            return ""
        i += 2
    return "".join(out)


def _direct_pair(function: str, region: str, source: Path) -> RenderPair | None:
    """Parse the exact standalone ``entry ++ emitProgram`` theorem shape."""

    # Collapse layout only; the quoted prefix remains escaped and is decoded
    # below.  The RHS must contain exactly one concatenation after the LHS:
    # ``++`` in the tail means this is a bundle/factor, not a standalone
    # render.  This excludes dispatchLoopLabeledFunction and .globl wrappers.
    compact = re.sub(r"\s+", " ", region).strip()
    equal = compact.find("=")
    if equal < 0:
        return None
    rhs = compact[equal + 1 :]
    if rhs.endswith(":= rfl"):
        rhs = rhs[: -len(":= rfl")].rstrip()
    if "++" not in rhs:
        return None
    prefix, tail = rhs.split("++", 1)
    prefix = prefix.strip()
    tail = tail.strip()
    prefix_match = re.fullmatch(r'"((?:[^"\\]|\\.)*)"', prefix)
    if prefix_match is None or "++" in tail:
        return None
    emit_match = re.fullmatch(r"emitProgramR?\s+(.+)", tail)
    if emit_match is None:
        return None

    decoded = _decode_string(prefix_match.group(1))
    if not decoded.endswith(":\n"):
        return None
    entry = decoded[:-2]
    # A standalone entry is a linker symbol.  Dot-prefixed local labels and
    # directives are factors/exports, not GuestImageEntries keys.
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", entry):
        return None

    program_match = re.search(
        r"\(?\s*(?:[A-Za-z_][A-Za-z0-9_]*\.)*"
        r"(?P<program>[A-Za-z_][A-Za-z0-9_]*_prog(?:_of)?)\b",
        emit_match.group(1),
    )
    if program_match is None:
        return None
    return RenderPair(function, entry, program_match.group("program"), source)


def discover_pairs(source_root: Path = SOURCE_ROOT) -> tuple[list[RenderPair], list[str]]:
    """Discover standalone Function/Program render pairs and parser errors."""

    pairs: list[RenderPair] = []
    errors: list[str] = []
    for source in sorted(source_root.rglob("*.lean")):
        text = source.read_text()
        definitions = {m.group("function") for m in FUNCTION_DEF.finditer(text)}
        for theorem in THEOREM_START.finditer(text):
            function = theorem.group("function")
            region = _theorem_region(text, theorem.start())
            if region is None:
                errors.append(f"{source}: {function}_eq_prog has no `:= rfl`")
                continue
            pair = _direct_pair(function, region, source)
            if pair is None:
                # Non-standalone render factors are intentionally outside this
                # gate; they are covered by the composition-specific checks.
                continue
            if function not in definitions:
                errors.append(
                    f"{source}: {function}_eq_prog has a standalone render but "
                    "no matching Function definition"
                )
                continue
            pairs.append(pair)
    return pairs, errors


def read_gie(path: Path = ENTRIES) -> dict[str, str]:
    """Return ``entry symbol -> Program`` from GuestImageEntries."""

    if not path.is_file():
        raise RuntimeError(f"missing GuestImageEntries: {path}")
    row = re.compile(
        r"\(GuestAddrs\.(?P<entry>[A-Za-z_][A-Za-z0-9_]*),\s*"
        r"(?P<program>[A-Za-z_][A-Za-z0-9_]*)\)"
    )
    out: dict[str, str] = {}
    for match in row.finditer(path.read_text()):
        entry = match.group("entry")
        program = match.group("program")
        old = out.get(entry)
        if old is not None and old != program:
            raise RuntimeError(
                f"duplicate GuestAddrs.{entry} rows: {old!r} and {program!r}"
            )
        out[entry] = program
    if not out:
        raise RuntimeError(f"no GuestImageEntries rows parsed from {path}")
    return out


def _program_stem(program: str) -> str:
    # ``emitProgramR (foo_prog_of .zero)`` is the relocatable form of the same
    # Program named ``foo_prog`` in GuestImageEntries.
    return re.sub(r"_of$", "", program)


def check_coverage(
    source_root: Path = SOURCE_ROOT,
    entries_path: Path = ENTRIES,
    fixture_dir: Path = FIXTURES,
    floor: int = EXPECTED_GUARDED_PAIRS_FLOOR,
) -> tuple[list[RenderPair], list[str]]:
    """Return discovered pairs and hard findings for the supplied tree."""

    pairs, parser_errors = discover_pairs(source_root)
    findings = list(parser_errors)
    if len(pairs) < floor:
        findings.append(
            "guarded render discovery fell below its floor: "
            f"{len(pairs)} pair(s), expected at least {floor}; "
            "the source scan may have gone silent"
        )
    gie = read_gie(entries_path)
    fixtures = {path.stem for path in fixture_dir.glob("*.s")}
    for pair in sorted(pairs, key=lambda item: (item.function, str(item.source))):
        has_fixture = pair.function in fixtures
        gie_program = gie.get(pair.entry)
        has_gie = gie_program is not None
        if has_gie and gie_program != _program_stem(pair.program):
            findings.append(
                f"{pair.function} ({pair.entry}) has GuestImageEntries program "
                f"{gie_program!r}, expected {_program_stem(pair.program)!r}"
            )
        if not has_fixture and not has_gie:
            findings.append(
                f"{pair.function} ({pair.entry}, {pair.program}) has neither "
                "GuestImageEntries row nor asm fixture"
            )
    return pairs, findings


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def self_test() -> int:
    """Exercise discovery, both oracle naming conventions, and the floor."""

    with tempfile.TemporaryDirectory(prefix="render-oracle-selftest-") as raw:
        root = Path(raw)
        sources = root / "EvmAsm" / "Codegen"
        sources.mkdir(parents=True)
        source = sources / "Sample.lean"
        source.write_text(
            'def fooFunction : String := "foo_bar:\\n" ++ emitProgram foo_prog\n'
            'theorem fooFunction_eq_prog :\n'
            '  fooFunction = "foo_bar:\\n" ++ emitProgram foo_prog := rfl\n'
            'def barFunction : String := "bar_baz:\\n" ++ emitProgramR bar_prog relocs\n'
            'theorem barFunction_eq_prog :\n'
            '  barFunction = "bar_baz:\\n" ++ emitProgramR bar_prog relocs := rfl\n'
            # Non-standalone factors must not enlarge the expected population.
            'def factorFunction : String := ".factor:\\n" ++ emitProgram factor_prog\n'
            'theorem factorFunction_eq_prog :\n'
            '  factorFunction = ".factor:\\n" ++ emitProgram factor_prog ++ "\\n" := rfl\n'
        )
        entries = root / "GuestImageEntries.lean"
        entries.write_text("(GuestAddrs.wrong_name, unrelated_prog),\n")
        fixtures = root / "fixtures"
        fixtures.mkdir()

        pairs, errors = discover_pairs(sources)
        _assert(not errors, f"self-test parser errors: {errors}")
        _assert({p.function for p in pairs} == {"barFunction", "fooFunction"},
                f"standalone discovery mismatch: {pairs}")

        # Wrong-side names must not cover either pair: fixture keys are Function
        # names and GIE keys are emitted entry symbols.
        _, findings = check_coverage(sources, entries, fixtures, floor=2)
        _assert(len(findings) == 2 and all("neither" in f for f in findings),
                f"self-test missing-oracle findings: {findings}")

        (fixtures / "barFunction.s").write_text("bar_baz:\n")
        _, findings = check_coverage(sources, entries, fixtures, floor=2)
        _assert(len(findings) == 1 and "fooFunction" in findings[0],
                f"fixture-side coverage mismatch: {findings}")

        entries.write_text("(GuestAddrs.foo_bar, foo_prog),\n")
        _, findings = check_coverage(sources, entries, fixtures, floor=2)
        _assert(findings == [], f"both oracle surfaces should cover: {findings}")

        # Discovery silence is a hard failure even when no pair is missing an
        # oracle, so a broken source walk cannot report a false clean result.
        empty = root / "empty"
        empty.mkdir()
        _, findings = check_coverage(empty, entries, fixtures, floor=1)
        _assert(any("fell below its floor" in f for f in findings),
                f"discovery floor did not fire: {findings}")

    print("check-render-oracle-coverage --self-test: OK — standalone discovery, "
          "Function-vs-entry naming, and the discovery floor all fail closed.")
    return 0


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        try:
            return self_test()
        except (AssertionError, RuntimeError, OSError) as exc:
            print(f"check-render-oracle-coverage --self-test: FAIL — {exc}",
                  file=sys.stderr)
            return 1

    try:
        pairs, findings = check_coverage()
    except (RuntimeError, OSError) as exc:
        print(f"check-render-oracle-coverage: FATAL — {exc}", file=sys.stderr)
        return 1
    print(
        f"check-render-oracle-coverage: discovered {len(pairs)} standalone "
        f"guarded render pair(s) (floor {EXPECTED_GUARDED_PAIRS_FLOOR})"
    )
    if findings:
        print(
            f"check-render-oracle-coverage: FAIL — {len(findings)} finding(s)",
            file=sys.stderr,
        )
        for finding in findings:
            print(f"  ✗ {finding}", file=sys.stderr)
        return 1
    print(
        "check-render-oracle-coverage: OK — every standalone pair has a "
        "GuestImageEntries row or Function-named asm fixture"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
