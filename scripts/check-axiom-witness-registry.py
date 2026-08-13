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
separate, still-open type-based census in #12210.  The write path refuses to
shrink an existing baseline unless the caller supplies an explicit, recorded
reason.  Otherwise a routine refresh could erase the very entry the ratchet
is meant to protect.

Usage::

    python3 scripts/check-axiom-witness-registry.py
    python3 scripts/check-axiom-witness-registry.py --self-test
    python3 scripts/check-axiom-witness-registry.py --write-allowlist
    python3 scripts/check-axiom-witness-registry.py --write-allowlist \
        --initialize-allowlist
    python3 scripts/check-axiom-witness-registry.py --write-allowlist \
        --allow-shrink "PR #NNNN: reviewed witness removal"

``--self-test`` proves the *shrink* lane can fire (#12210): delete one
registry witness binding, assert the check exits non-zero, restore, assert
exit 0. The grow path was observed in the wild (#12258); the shrink path had
never been exercised — the one-sided-detector shape.
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


def baseline_has_entries() -> bool:
    """Return whether the checked-in baseline contains at least one name."""
    if not EXPECTED.is_file():
        return False
    return any(
        line.strip() and not line.lstrip().startswith("#")
        for line in EXPECTED.read_text().splitlines()
    )


def compare_sets(current: set[str], expected: set[str], *, quiet: bool = False) -> int:
    """Return 0 iff the sets match; 1 and (unless quiet) print the diff otherwise."""
    missing = sorted(expected - current)
    extra = sorted(current - expected)
    if missing or extra:
        if not quiet:
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
    if not quiet:
        print(
            "check-axiom-witness-registry: OK — "
            f"{len(current)} registry witness names match the pinned set"
        )
    return 0


def self_test() -> int:
    """Inject a registry shrink; the check must FAIL then PASS after restore.

    Mutates a real Progress registry file (not the baseline): removing a
    ``:= @EvmAsm.…`` binding is exactly the silent-erosion path the pin exists
    to catch. Verdict flip is the acceptance criterion — a printed message alone
    is the #12195 failure mode.
    """
    expected = expected_names()
    current = current_names()
    if compare_sets(current, expected, quiet=True) != 0:
        print(
            "check-axiom-witness-registry --self-test: FAIL — tree already dirty "
            "before inject; census first",
            file=sys.stderr,
        )
        return 1

    canary = sorted(expected)[0]
    needle = f"@{canary}"
    target: Path | None = None
    original: str | None = None
    for path in REGISTRIES:
        text = path.read_text()
        # Require the witness-binding shape, not prose that names the theorem.
        if re.search(r":=\s*" + re.escape(needle), text) is None:
            continue
        target = path
        original = text
        break
    if target is None or original is None:
        print(
            f"check-axiom-witness-registry --self-test: FAIL — cannot locate "
            f"binding for canary {canary}",
            file=sys.stderr,
        )
        return 1

    # Break the WITNESS_RE match without leaving a syntactically identical @EvmAsm name.
    mutated, n = re.subn(
        r":=\s*" + re.escape(needle),
        ":= @__self_test_removed__." + canary.rsplit(".", 1)[-1],
        original,
        count=1,
    )
    if n != 1:
        print(
            f"check-axiom-witness-registry --self-test: FAIL — expected one "
            f"binding rewrite for {canary}, got {n}",
            file=sys.stderr,
        )
        return 1

    try:
        target.write_text(mutated)
        if canary in current_names():
            print(
                f"check-axiom-witness-registry --self-test: FAIL — inject did "
                f"not remove {canary} from the parsed set",
                file=sys.stderr,
            )
            return 1
        if compare_sets(current_names(), expected, quiet=True) == 0:
            print(
                "check-axiom-witness-registry --self-test: FAIL — shrunk "
                f"registry still compared equal (canary {canary}); the "
                "checker cannot see shrinks",
                file=sys.stderr,
            )
            return 1
    finally:
        target.write_text(original)

    if compare_sets(current_names(), expected, quiet=True) != 0:
        print(
            "check-axiom-witness-registry --self-test: FAIL — restore left "
            "the tree dirty",
            file=sys.stderr,
        )
        return 1

    print(
        f"check-axiom-witness-registry --self-test: OK — delete {canary} "
        f"from {target.relative_to(ROOT)} fails; restore exits 0"
    )
    return 0


def write_allowlist(names: set[str], shrink_reason: str | None = None) -> None:
    header = (
        "# #12210 expected axiom-witness registry, sorted by qualified name\n"
        "# Regenerate only when a reviewed registry addition/removal lands:\n"
        "#   python3 scripts/check-axiom-witness-registry.py --write-allowlist\n"
        "# The list is independent of AxiomWitnesses.lean, which is generated\n"
        "# from the registries and therefore cannot serve as its own baseline.\n"
        "\n"
    )
    if shrink_reason is not None:
        if "\n" in shrink_reason or "\r" in shrink_reason:
            raise SystemExit(
                "check-axiom-witness-registry: shrink reason must be one line"
            )
        header += f"# Explicit shrink authorization: {shrink_reason}\n"
    EXPECTED.write_text(header + "".join(f"{name}\n" for name in sorted(names)))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--self-test",
        action="store_true",
        help=(
            "inject a registry shrink and assert the check fails then passes "
            "after restore (non-vacuity)"
        ),
    )
    parser.add_argument(
        "--write-allowlist",
        action="store_true",
        help="rewrite the checked-in expected set from the current registries",
    )
    parser.add_argument(
        "--allow-shrink",
        metavar="REASON",
        help=(
            "authorize removing names from an existing baseline and record the "
            "one-line reason in its header"
        ),
    )
    parser.add_argument(
        "--initialize-allowlist",
        action="store_true",
        help="explicitly create a missing or empty baseline",
    )
    args = parser.parse_args()

    if args.self_test and (
        args.write_allowlist or args.allow_shrink is not None or args.initialize_allowlist
    ):
        parser.error("--self-test cannot accompany write-allowlist options")

    if args.self_test:
        return self_test()

    if args.initialize_allowlist and not args.write_allowlist:
        parser.error("--initialize-allowlist requires --write-allowlist")

    current = current_names()
    if args.write_allowlist:
        if not baseline_has_entries():
            if not args.initialize_allowlist:
                print(
                    "check-axiom-witness-registry: REFUSE — baseline is missing "
                    "or empty; rerun with --initialize-allowlist in a reviewed "
                    "initialization change",
                    file=sys.stderr,
                )
                return 1
            if args.allow_shrink is not None:
                print(
                    "check-axiom-witness-registry: REFUSE — "
                    "--allow-shrink cannot accompany initialization",
                    file=sys.stderr,
                )
                return 1
            write_allowlist(current)
            print(
                "check-axiom-witness-registry: initialized "
                f"{EXPECTED.relative_to(ROOT)} ({len(current)} names)"
            )
            return 0

        if args.initialize_allowlist:
            print(
                "check-axiom-witness-registry: REFUSE — baseline already has "
                "entries; --initialize-allowlist is only for first setup",
                file=sys.stderr,
            )
            return 1

        previous = expected_names()
        removed = sorted(previous - current) if previous is not None else []
        if removed and args.allow_shrink is None:
            print(
                "check-axiom-witness-registry: REFUSE — --write-allowlist "
                "would shrink the existing baseline; rerun with "
                "--allow-shrink '<reviewed reason>'",
                file=sys.stderr,
            )
            for name in removed:
                print(f"  removed: {name}", file=sys.stderr)
            return 1
        if args.allow_shrink is not None and not args.allow_shrink.strip():
            print(
                "check-axiom-witness-registry: REFUSE — --allow-shrink "
                "requires a non-empty one-line reason",
                file=sys.stderr,
            )
            return 1
        if args.allow_shrink is not None and not removed:
            print(
                "check-axiom-witness-registry: REFUSE — --allow-shrink was "
                "given but no baseline names would be removed",
                file=sys.stderr,
            )
            return 1
        write_allowlist(current, args.allow_shrink)
        print(
            "check-axiom-witness-registry: wrote "
            f"{EXPECTED.relative_to(ROOT)} ({len(current)} names)"
        )
        return 0

    return compare_sets(current, expected_names())


if __name__ == "__main__":
    sys.exit(main())
