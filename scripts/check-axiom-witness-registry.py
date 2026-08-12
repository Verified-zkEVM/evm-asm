#!/usr/bin/env python3
"""Pin the *set* of registry axiom witnesses (#12210).

``check-axioms.sh`` proves that every witness currently present in the three
progress registries emitted one ``#print axioms`` report.  The registries are
also the input to the generator, however, so deleting a row shrinks both sides
of that comparison.  This check supplies the independent expected set: a
sorted, checked-in list of witness declarations.  A missing name is a silent
shrink; an unexpected name is a deliberate registry expansion that must pin
the new set in the same change.

This is intentionally a source-only guard.  It does not build Lean and does
not decide whether an unregistered theorem *ought* to be a witness; that is the
separate, still-open type-based census in #12210.

Usage::

    python3 scripts/check-axiom-witness-registry.py
    python3 scripts/check-axiom-witness-registry.py --write-allowlist
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REGISTRIES = (
    ROOT / "EvmAsm" / "Progress.lean",
    ROOT / "EvmAsm" / "Progress" / "Routines.lean",
    ROOT / "EvmAsm" / "Progress" / "Correspondence.lean",
)
EXPECTED = ROOT / "scripts" / "axiom-witness-registry-allow.txt"

# Match the actual abbrev binding, not prose that happens to mention a fully
# qualified theorem.  Flattening is unnecessary here: the declaration target
# is on the same line in the checked-in registries, while the baseline itself
# is the durable source of expected names.
WITNESS_RE = re.compile(r":=\s*@EvmAsm\.[A-Za-z0-9_.']+")


def current_names() -> set[str]:
    names: set[str] = set()
    for path in REGISTRIES:
        text = path.read_text()
        for match in WITNESS_RE.finditer(text):
            names.add(match.group(0).split("@", 1)[1])
    if not names:
        raise SystemExit("check-axiom-witness-registry: no witness bindings found")
    return names


def expected_names() -> set[str]:
    if not EXPECTED.is_file():
        raise SystemExit(f"check-axiom-witness-registry: missing {EXPECTED}")
    ordered: list[str] = []
    for line in EXPECTED.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "\t" in line or " " in line:
            raise SystemExit(
                "check-axiom-witness-registry: malformed baseline line "
                f"(one qualified name expected): {line!r}"
            )
        ordered.append(line)
    if not ordered:
        raise SystemExit("check-axiom-witness-registry: empty baseline")
    if ordered != sorted(ordered):
        raise SystemExit(
            "check-axiom-witness-registry: baseline is not sorted; "
            "run --write-allowlist in the reviewed registry change"
        )
    if len(set(ordered)) != len(ordered):
        raise SystemExit("check-axiom-witness-registry: baseline contains duplicates")
    return set(ordered)


def write_allowlist(names: set[str]) -> None:
    header = (
        "# #12210 expected axiom-witness registry, sorted by qualified name\n"
        "# Regenerate only when a reviewed registry addition/removal lands:\n"
        "#   python3 scripts/check-axiom-witness-registry.py --write-allowlist\n"
        "# The list is independent of AxiomWitnesses.lean, which is generated\n"
        "# from the registries and therefore cannot serve as its own baseline.\n"
        "\n"
    )
    EXPECTED.write_text(header + "".join(f"{name}\n" for name in sorted(names)))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-allowlist",
        action="store_true",
        help="rewrite the checked-in expected set from the current registries",
    )
    args = parser.parse_args()

    current = current_names()
    if args.write_allowlist:
        write_allowlist(current)
        print(
            "check-axiom-witness-registry: wrote "
            f"{EXPECTED.relative_to(ROOT)} ({len(current)} names)"
        )
        return 0

    expected = expected_names()
    missing = sorted(expected - current)
    extra = sorted(current - expected)
    if missing or extra:
        print(
            "check-axiom-witness-registry: FAIL — registry set differs from "
            f"{EXPECTED.relative_to(ROOT)} (current={len(current)} "
            f"expected={len(expected)})",
            file=sys.stderr,
        )
        if missing:
            print("  missing from current registries:", file=sys.stderr)
            for name in missing:
                print(f"    {name}", file=sys.stderr)
        if extra:
            print("  new in current registries:", file=sys.stderr)
            for name in extra:
                print(f"    {name}", file=sys.stderr)
        print(
            "  Update the baseline only with a reviewed registry change; "
            "never make the generator's output its own expectation.",
            file=sys.stderr,
        )
        return 1

    print(
        "check-axiom-witness-registry: OK — "
        f"{len(current)} registry witness names match the pinned set"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
