#!/usr/bin/env python3
"""Census references to a symbol in relocatable build-unit objects.

The final guest ELF is normally ET_EXEC, so its relocations have already been
resolved and ``readelf -r`` cannot prove that a static arena was referenced.
This tool deliberately consumes ET_REL objects instead.  It reports three
answers:

* ``referenced`` when at least one relocation names the requested symbol;
* ``not-referenced`` when every scanned object was a readable ET_REL file and
  no relocation named it; and
* ``cannot-tell`` when an input is missing, unreadable, not ET_REL, or no
  objects were found.

``cannot-tell`` is intentionally a first-class result.  An absent object must
not silently become evidence that a symbol is dead.

Coverage gaps (not proofs of deadness)
--------------------------------------
This is a reachability aid, not a proof that a definition is semantically
   unused.  Two gaps sit above the tool by construction:

1. **Fallthrough control flow (hot path).**  A label reached only by falling
   through from the preceding instruction has no branch and no JAL
   relocation.  Local / dotted labels (``.L…``, ``.runtime_…``) are exactly
   where fallthrough is common, and the tool's most natural question is
   whether such a label is dead.  ``not-referenced`` therefore does **not**
   rule out fallthrough reachability; every ``not-referenced`` answer for a
   dotted name prints an explicit caveat line so the status cannot be
   mistaken for a deadness proof.  Detecting fallthrough would need
   disassembly adjacency (is the preceding instruction non-terminating?) —
   deliberately not attempted here; a cheap honest caveat beats an expensive
   partial detector (#11271).  Witness: ``.runtime_tx_auth_state_used_done``
   is live via fallthrough from ``.runtime_tx_auth_state_refund_done`` and
   has no relocation.

2. **Constant folding (rarer).**  Values folded into instruction immediates
   leave no symbol relocation (e.g. ``accountWriteHasState``).  Documented
   here only; less common than asking about a control-flow label.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Reference:
    obj: Path
    section: str
    offset: str
    relocation_type: str


def run_readelf(*args: str) -> tuple[int, str, str]:
    proc = subprocess.run(
        ["readelf", *args],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return proc.returncode, proc.stdout, proc.stderr


def object_type(path: Path) -> str | None:
    code, stdout, _ = run_readelf("-h", "--wide", str(path))
    if code != 0:
        return None
    for line in stdout.splitlines():
        if line.strip().startswith("Type:"):
            return line.split(":", 1)[1].strip()
    return None


def relocations(path: Path, symbol: str) -> tuple[list[Reference], str | None]:
    """Return matching relocations and an error string, if the input is unusable."""

    if not path.is_file():
        return [], f"missing object: {path}"
    kind = object_type(path)
    if kind is None:
        return [], f"cannot read ELF header: {path}"
    if not kind.startswith("REL ") and "Relocatable file" not in kind:
        return [], f"not a relocatable ET_REL object: {path} ({kind})"

    code, stdout, stderr = run_readelf("-r", "--wide", str(path))
    if code != 0:
        detail = stderr.strip() or "readelf -r failed"
        return [], f"cannot read relocations from {path}: {detail}"

    refs: list[Reference] = []
    section = "?"
    for line in stdout.splitlines():
        section_match = re.match(r"Relocation section '([^']+)'", line)
        if section_match:
            section = section_match.group(1)
            continue
        fields = line.split()
        if len(fields) < 5 or not re.fullmatch(r"[0-9a-fA-F]+", fields[0]):
            continue
        if fields[4] == symbol:
            refs.append(
                Reference(
                    obj=path,
                    section=section,
                    offset=fields[0],
                    relocation_type=fields[2],
                )
            )
    return refs, None


def expand_paths(raw_paths: list[str]) -> tuple[list[Path], list[str]]:
    paths: list[Path] = []
    errors: list[str] = []
    for raw in raw_paths:
        path = Path(raw)
        if path.is_dir():
            found = sorted(path.rglob("*.o"))
            if not found:
                errors.append(f"no .o objects found under: {path}")
            paths.extend(found)
        elif path.exists():
            paths.append(path)
        else:
            errors.append(f"missing input: {path}")
    # A directory and an explicitly listed object can overlap; scan once.
    return sorted(set(paths)), errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Census symbol relocations in ET_REL build-unit objects."
    )
    parser.add_argument("symbol", help="exact symbol name to search for")
    parser.add_argument(
        "objects",
        nargs="+",
        metavar="OBJECT_OR_DIR",
        help="ET_REL .o file(s), or directories searched recursively for .o files",
    )
    args = parser.parse_args(argv)

    objects, expansion_errors = expand_paths(args.objects)
    references: list[Reference] = []
    errors = list(expansion_errors)
    for obj in objects:
        refs, error = relocations(obj, args.symbol)
        references.extend(refs)
        if error is not None:
            errors.append(error)

    if errors or not objects:
        status = "cannot-tell"
    elif references:
        status = "referenced"
    else:
        status = "not-referenced"

    print(f"symbol: {args.symbol}")
    print(f"status: {status}")
    print(f"objects_scanned: {len(objects)}")
    for ref in sorted(references, key=lambda item: (str(item.obj), item.offset)):
        print(
            "reference: "
            f"object={ref.obj} section={ref.section} "
            f"offset=0x{ref.offset} relocation={ref.relocation_type}"
        )
    # Fallthrough has no relocation by construction (#11271).  Emit the caveat
    # on not-referenced answers for dotted/local labels (the hot path) so label
    # deadness cannot be inferred from status alone.  Global data symbols still
    # carry the constant-folding non-proof in the module docstring.
    if status == "not-referenced" and args.symbol.startswith("."):
        print(
            "caveat: not-referenced does not rule out fallthrough reachability "
            "for labels (no branch/JAL relocation by construction)"
        )
    for error in errors:
        print(f"error: {error}", file=sys.stderr)

    # Referenced and not-referenced are answers, not failures.  An unusable
    # input is non-zero so callers cannot accidentally treat it as a negative.
    return 2 if status == "cannot-tell" else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
