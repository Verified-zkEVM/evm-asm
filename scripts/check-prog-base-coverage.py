#!/usr/bin/env python3
"""Check that relocatable converted ``_prog`` entries have a tested base.

GH #13183 found that ``dispatchLoop_prog`` had a kernel-checked symbolic
render and a relocatable Program, but no ``GuestImageEntries`` row.  The
``emitProgramR`` tie and a standalone assembler comparison cannot see the
Program's PC base.  The post-link byte gate does see a base, but only after a
Program has been registered, so an unregistered converted Program can be
wrong without any gate noticing.

This check is intentionally the cheap middle cross-reference:

* conversion entries come from the asm-fixture MANIFEST and explicit
  ``*_eq_prog`` render ties (the latter covers hand-maintained conversions such
  as the dispatcher body);
* ``laHi``/``laLo``/``jalOff`` in the Program declaration identify a PC/base
  dependent conversion;
* ``symbol-addresses.tsv`` identifies entries that are actually linked into
  ``stateless_guest``; and
* ``GuestImageEntries.lean`` identifies entries whose base is exercised by the
  post-link Program-byte check.

Only a reloc-bearing converted entry that is linked and unrowed is a finding.
Unlinked conversions remain visible in the census but are not failures: the
image cannot exercise their base.  The source scan has a lower-bound floor so
an accidentally silent parser cannot turn the gate green.

``--self-test`` uses a temporary synthetic source tree and demonstrates the
whole detector: a planted linked dotted-label Program passes when rowed, fails
when its row is removed, and passes again when restored.  No repository file
is modified by the self-test.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CODEGEN = REPO / "EvmAsm" / "Codegen"
MANIFEST = REPO / "scripts" / "asm-fixtures" / "MANIFEST.tsv"
ENTRIES = CODEGEN / "Proofs" / "GuestImageEntries.lean"
SYMBOLS = REPO / "scripts" / "asm-fixtures" / "symbol-addresses.tsv"

# Lower bounds, not claims of exact population.  They are deliberately below
# today's measured 561 converted and 433 reloc-bearing conversion entries: adding a
# conversion is harmless, while a parser going quiet must fail loudly.
MIN_CONVERTED = 550
MIN_RELOC_CONVERTED = 400

NAME = r"[A-Za-z_][A-Za-z0-9_']*"
PROG = NAME + r"_prog(?:_of)?"

# Same direct Function shape used by guest_image_coverage.py.  This is only
# used to identify MANIFEST-bound conversions; the declaration body is looked
# up independently below so a binding cannot make a missing Program invisible.
FUNCTION_BINDING_RE = re.compile(
    r"def\s+(?P<function>" + NAME + r"Function)\s*:\s*String\s*:=\s*"
    r"(?:\n\s*)?"
    r"(?:\"\s*\.globl\s+[A-Za-z0-9_.]+\\n\"\s*\+\+\s*)?"
    r'"(?P<entry>[A-Za-z0-9_.]+):\\n"\s*\+\+\s*'
    r"emitProgramR?\s+(?:\(\s*)?(?P<program>" + PROG + r")"
)

THEOREM_RE = re.compile(r"(?m)^\s*theorem\s+" + NAME + r"_eq_prog\b")
TOP_DECL_RE = re.compile(
    r"(?m)^(?:def|abbrev|theorem|lemma|instance|namespace|section|end)\b"
)
ENTRY_LITERAL_RE = re.compile(r'"(?P<entry>(?:[^"\\]|\\.)*):\\n"')
EMIT_PROGRAM_RE = re.compile(
    r"\bemitProgramR?\s+(?:\(\s*)?(?P<program>" + PROG + r")\b"
)
PROG_DECL_RE = re.compile(
    r"(?m)^(?:def|abbrev)\s+(?P<name>" + PROG + r")\b[^\n]*:\s*Program\b"
)
RELOC_RE = re.compile(r"\b(laHi|laLo|jalOff)\b")
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)


@dataclass(frozen=True)
class Candidate:
    entry: str
    program: str
    source: str
    reloc_kinds: tuple[str, ...]


def normalize_program(name: str) -> str:
    return name[:-3] if name.endswith("_of") else name


def ga_name(symbol: str) -> str:
    """Match asm_to_program's GuestAddrs spelling for dotted local labels."""

    return symbol[1:] if symbol.startswith(".") else symbol


def code_without_comments(text: str) -> str:
    """Keep relocation tokens in code, not explanatory comments."""

    text = BLOCK_COMMENT_RE.sub("", text)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def parse_manifest(text: str) -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    for line_no, raw in enumerate(text.splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 2 or not fields[0] or not fields[1]:
            raise ValueError(f"MANIFEST line {line_no} is not two tab-separated fields")
        rows.append((fields[0], fields[1]))
    if not rows:
        raise ValueError("MANIFEST has no conversion rows")
    return rows


def parse_function_bindings(text: str) -> dict[str, tuple[str, str]]:
    out: dict[str, tuple[str, str]] = {}
    for match in FUNCTION_BINDING_RE.finditer(text):
        function = match.group("function")
        binding = (match.group("entry"), normalize_program(match.group("program")))
        old = out.get(function)
        if old is not None and old != binding:
            raise ValueError(f"duplicate Function binding for {function}")
        out[function] = binding
    return out


def all_function_bindings(
    source_texts: dict[str, str],
) -> tuple[dict[str, tuple[str, str, str]], list[str]]:
    """Collect Function bindings from bridge files and their imported leaves."""

    out: dict[str, tuple[str, str, str]] = {}
    errors: list[str] = []
    for source, text in source_texts.items():
        for function, binding in parse_function_bindings(text).items():
            old = out.get(function)
            value = (binding[0], binding[1], source)
            if old is not None and old[:2] != value[:2]:
                errors.append(
                    f"conflicting Function binding for {function}: "
                    f"{old[0]} / {old[1]} versus {value[0]} / {value[1]}"
                )
            else:
                out.setdefault(function, value)
    return out, errors


def declaration_region(text: str, start: int) -> str:
    next_decl = TOP_DECL_RE.search(text, start + 1)
    return text[start : next_decl.start() if next_decl else len(text)]


def parse_manual_pairs(text: str) -> list[tuple[str, str]]:
    """Find explicit render ties not necessarily represented in MANIFEST."""

    out: list[tuple[str, str]] = []
    for theorem in THEOREM_RE.finditer(text):
        region = declaration_region(text, theorem.start())
        emit = EMIT_PROGRAM_RE.search(region)
        if emit is None:
            continue
        entry = ENTRY_LITERAL_RE.search(region)
        if entry is None:
            continue
        out.append((entry.group("entry"), normalize_program(emit.group("program"))))
    return out


def program_declarations(
    source_texts: dict[str, str],
) -> dict[str, list[tuple[str, str, str]]]:
    """program -> [(raw declaration name, source path, declaration body)]."""

    out: dict[str, list[tuple[str, str, str]]] = {}
    for source, text in source_texts.items():
        matches = list(PROG_DECL_RE.finditer(text))
        for match in matches:
            next_decl = TOP_DECL_RE.search(text, match.end())
            end = next_decl.start() if next_decl is not None else len(text)
            raw_name = match.group("name")
            normalized = normalize_program(raw_name)
            out.setdefault(normalized, []).append(
                (raw_name, source, text[match.start() : end])
            )
    return out


def discover_candidates(
    manifest_text: str,
    source_texts: dict[str, str],
) -> tuple[list[Candidate], list[str]]:
    """Discover MANIFEST and explicit manual conversions plus parse their bodies."""

    errors: list[str] = []
    manifest = parse_manifest(manifest_text)
    declarations = program_declarations(source_texts)
    bindings, binding_errors = all_function_bindings(source_texts)
    errors.extend(binding_errors)
    seeds: dict[tuple[str, str], str] = {}

    for function, source in manifest:
        binding = bindings.get(function)
        if binding is None:
            if source not in source_texts:
                errors.append(f"MANIFEST binding {function}: missing source {source}")
            else:
                errors.append(
                    f"MANIFEST binding {function}: Function definition not parsed in {source}"
                )
            continue
        entry, program, binding_source = binding
        if source not in source_texts:
            errors.append(
                f"MANIFEST binding {function}: missing source {source}"
            )
        seeds.setdefault((entry, program), binding_source)

    for source, text in source_texts.items():
        for entry, program in parse_manual_pairs(text):
            seeds.setdefault((entry, program), source)

    candidates: list[Candidate] = []
    for (entry, program), source_hint in sorted(seeds.items()):
        decls = declarations.get(program, [])
        if not decls:
            errors.append(f"{source_hint}: no Program declaration found for {program}")
            continue
        preferred = [d for d in decls if d[1] == source_hint]
        _raw_name, source, body = (preferred or decls)[0]
        reloc_kinds = tuple(sorted(set(RELOC_RE.findall(code_without_comments(body)))))
        candidates.append(Candidate(entry, program, source, reloc_kinds))
    return candidates, errors


def read_gie(text: str) -> dict[str, str]:
    row_re = re.compile(
        r"\(GuestAddrs\.(?P<entry>[A-Za-z_][A-Za-z0-9_']*),\s*"
        r"(?P<program>[A-Za-z_][A-Za-z0-9_']*)\)"
    )
    rows: dict[str, str] = {}
    for match in row_re.finditer(text):
        entry, program = match.group("entry"), match.group("program")
        old = rows.get(entry)
        if old is not None and old != program:
            raise ValueError(f"GuestImageEntries has conflicting rows for {entry}")
        rows[entry] = program
    if not rows:
        raise ValueError("GuestImageEntries has no rows")
    return rows


def read_linked_text_symbols(text: str) -> set[str]:
    symbols: set[str] = set()
    for line_no, raw in enumerate(text.splitlines(), 1):
        if not raw.strip() or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) < 5:
            raise ValueError(
                f"symbol-addresses.tsv line {line_no} has fewer than 5 fields"
            )
        if (
            fields[0] == "stateless_guest"
            and fields[3] == ".text"
            and fields[1] != ".text"
        ):
            symbols.add(fields[1])
    if not symbols:
        raise ValueError("symbol-addresses.tsv has no stateless_guest .text symbols")
    return symbols


def evaluate(
    candidates: list[Candidate],
    rows: dict[str, str],
    linked: set[str],
    *,
    min_converted: int,
    min_reloc: int,
) -> tuple[list[str], dict[str, int]]:
    reloc = [candidate for candidate in candidates if candidate.reloc_kinds]
    linked_reloc = [candidate for candidate in reloc if candidate.entry in linked]
    unlinked_reloc = [candidate for candidate in reloc if candidate.entry not in linked]
    missing = [
        candidate
        for candidate in linked_reloc
        if ga_name(candidate.entry) not in rows
    ]
    findings = [
        f"linked reloc-bearing converted entry {candidate.entry!r} → "
        f"{candidate.program} ({candidate.source}) has no GuestImageEntries row"
        for candidate in sorted(missing, key=lambda item: (item.entry, item.program))
    ]
    if len(candidates) < min_converted:
        findings.append(
            f"converted discovery fell below its floor: {len(candidates)} < "
            f"{min_converted}; the source scan may have gone silent"
        )
    if len(reloc) < min_reloc:
        findings.append(
            f"reloc-bearing converted discovery fell below its floor: {len(reloc)} < "
            f"{min_reloc}; the relocation scan may have gone silent"
        )
    counts = {
        "converted": len(candidates),
        "reloc": len(reloc),
        "linked_reloc": len(linked_reloc),
        "unlinked_reloc": len(unlinked_reloc),
        "missing": len(missing),
        "rows": len(rows),
    }
    return findings, counts


def production_inputs() -> tuple[str, dict[str, str], str, str]:
    source_texts = {
        path.relative_to(REPO).as_posix(): path.read_text()
        for path in sorted(CODEGEN.rglob("*.lean"))
    }
    return MANIFEST.read_text(), source_texts, ENTRIES.read_text(), SYMBOLS.read_text()


def run_live() -> int:
    try:
        manifest, source_texts, entries_text, symbols_text = production_inputs()
        candidates, parse_errors = discover_candidates(manifest, source_texts)
        rows = read_gie(entries_text)
        linked = read_linked_text_symbols(symbols_text)
    except (OSError, ValueError) as exc:
        print(f"check-prog-base-coverage: FATAL — {exc}", file=sys.stderr)
        return 1

    if parse_errors:
        print(
            f"check-prog-base-coverage: FAIL — {len(parse_errors)} conversion parse error(s)",
            file=sys.stderr,
        )
        for error in parse_errors:
            print(f"  ✗ {error}", file=sys.stderr)
        return 1

    findings, counts = evaluate(
        candidates,
        rows,
        linked,
        min_converted=MIN_CONVERTED,
        min_reloc=MIN_RELOC_CONVERTED,
    )
    print(
        "check-prog-base-coverage: "
        f"converted={counts['converted']} reloc-bearing={counts['reloc']} "
        f"linked-reloc={counts['linked_reloc']} "
        f"unlinked-reloc={counts['unlinked_reloc']} "
        f"GuestImageEntries={counts['rows']} missing-row={counts['missing']}"
    )
    if findings:
        print(
            f"check-prog-base-coverage: FAIL — {len(findings)} finding(s)",
            file=sys.stderr,
        )
        for finding in findings:
            print(f"  ✗ {finding}", file=sys.stderr)
        return 1
    print(
        "check-prog-base-coverage: OK — every linked reloc-bearing converted "
        "Program has a GuestImageEntries base check"
    )
    return 0


def self_test() -> int:
    source = (
        'def fooFunction : String := ".foo_linked:\\n" ++ '
        "emitProgramR foo_prog foo_relocs\n"
        "def foo_prog : Program := [ .AUIPC .x5 (laHi GuestAddrs.foo_data "
        "(GuestAddrs.foo_linked + 0)) ]\n"
        'theorem fooFunction_eq_prog :\n'
        '  fooFunction = ".foo_linked:\\n" ++ '
        "emitProgramR foo_prog foo_relocs := rfl\n"
    )
    manifest = "fooFunction\tEvmAsm/Codegen/Sample.lean\n"
    symbols = (
        "# image\tsymbol\taddress\tsection\tstability\n"
        "stateless_guest\t.foo_linked\t0x80000000\t.text\tLINK_DEPENDENT\n"
    )
    try:
        candidates, errors = discover_candidates(
            manifest,
            {"EvmAsm/Codegen/Sample.lean": source},
        )
        if errors:
            raise AssertionError(f"synthetic parse errors: {errors}")
        linked = read_linked_text_symbols(symbols)
        rows = {"foo_linked": "foo_prog"}
        findings, _ = evaluate(candidates, rows, linked, min_converted=1, min_reloc=1)
        if findings:
            raise AssertionError(f"rowed synthetic control failed: {findings}")

        findings, _ = evaluate(candidates, {}, linked, min_converted=1, min_reloc=1)
        if len(findings) != 1 or "foo_linked" not in findings[0]:
            raise AssertionError(f"unrowed linked synthetic did not fail: {findings}")

        findings, _ = evaluate(
            candidates,
            {"foo_linked": "foo_prog"},
            linked,
            min_converted=1,
            min_reloc=1,
        )
        if findings:
            raise AssertionError(f"restored synthetic control failed: {findings}")
    except (AssertionError, ValueError, OSError) as exc:
        print(f"check-prog-base-coverage --self-test: FAIL — {exc}", file=sys.stderr)
        return 1

    print(
        "check-prog-base-coverage --self-test: OK — planted linked dotted-label "
        "Program passes when rowed, fails when unrowed, and passes after restore"
    )
    return 0


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    return run_live()


if __name__ == "__main__":
    raise SystemExit(main())
