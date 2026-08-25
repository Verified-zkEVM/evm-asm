#!/usr/bin/env python3
"""Census `.proven` theorem statements for stateful entry premises.

The progress notes are intentionally not an input to this scan.  It starts at
the `.proven` registry rows, locates each named theorem declaration, and then
expands the small assertion definitions named by those declarations.  The
expansion is what catches a ``bytesRegion ... (List.replicate 32 0)`` premise
hidden behind a caller-precondition abbreviation.

This is a static detector, not a soundness proof.  It reports fixed/global
regions and zero-filled byte regions for human classification; ordinary ABI
alignment and output postconditions are not findings by themselves.
"""

from __future__ import annotations

import argparse
import csv
import re
from pathlib import Path


ROUTINE_RE = re.compile(r'^\s*routine\s+"([^"]+)"\s+\.proven\b')
THEOREM_RE = re.compile(
    r'^\s*(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_\']+)\b'
)
DEF_RE = re.compile(r'^\s*(?:private\s+)?def\s+([A-Za-z0-9_\']+)\b')

DIRECT_PATTERNS = (
    ("zero-region", re.compile(
        r"bytesRegion\s+[A-Za-z0-9_]+\s+\(List\.replicate\s+32\s+\(0"
    )),
    ("fixed-global-memory", re.compile(
        r"\(GuestAddrs\.[A-Za-z0-9_]+\s*:\s*Word\)\s*↦ₘ"
    )),
    ("global-const", re.compile(r"\bglobalConst\b")),
    ("fixed-gp-memory", re.compile(r"\(gp\s*\+\s*[0-9]+\)\s*↦ₘ")),
)

EXPAND_NAMES = {
    "afpCallerPre": "AddressFromPubkeySpec.lean",
    "kssCallerPre": "HashBridgeKeccakSegTop.lean",
}


def source_lines(root: Path) -> list[tuple[Path, list[str]]]:
    return [(path, path.read_text(errors="replace").splitlines())
            for path in root.rglob("*.lean")]


def registry_rows(progress: Path) -> list[tuple[str, str]]:
    lines = progress.read_text().splitlines()
    rows: list[tuple[str, str]] = []
    current: str | None = None
    block: list[str] = []
    for line in lines + ['routine "__end__" .proven']:
        match = ROUTINE_RE.match(line)
        if match:
            if current is not None:
                rows.extend((current, theorem) for theorem in
                            re.findall(r'\(some\s+"([^"]+)"\)', "\n".join(block)))
            current = match.group(1)
            block = [line]
        elif current is not None:
            block.append(line)
    return rows


def declaration_blocks(files: list[tuple[Path, list[str]]], names: set[str]) -> dict[str, tuple[Path, int, str]]:
    found: dict[str, tuple[Path, int, str]] = {}
    for path, lines in files:
        for index, line in enumerate(lines):
            match = THEOREM_RE.match(line)
            if not match or match.group(1) not in names:
                continue
            end = min(len(lines), index + 700)
            block: list[str] = []
            for cursor in range(index, end):
                block.append(lines[cursor])
                if re.search(r':=\s*(?:by|sorry)\b', lines[cursor]):
                    break
            found.setdefault(match.group(1), (path, index + 1, "\n".join(block)))
    return found


def named_defs(files: list[tuple[Path, list[str]]]) -> dict[str, tuple[Path, int, str]]:
    found: dict[str, tuple[Path, int, str]] = {}
    for path, lines in files:
        for index, line in enumerate(lines):
            match = DEF_RE.match(line)
            if not match or match.group(1) not in EXPAND_NAMES:
                continue
            # Assertion definitions are short.  Stop at the next declaration
            # boundary, retaining enough text for the premise pattern.
            block = [line]
            cursor = index + 1
            while cursor < len(lines) and cursor < index + 160:
                if cursor > index + 1 and re.match(r'^\s*(?:/--|theorem|def|private def)\b', lines[cursor]):
                    break
                block.append(lines[cursor])
                cursor += 1
            found.setdefault(match.group(1), (path, index + 1, "\n".join(block)))
    return found


def hits(text: str) -> list[tuple[str, str]]:
    return [(label, pattern.pattern) for label, pattern in DIRECT_PATTERNS
            if pattern.search(text)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root
    rows = registry_rows(root / "Progress" / "Routines.lean")
    names = {theorem.rsplit(".", 1)[-1] for _, theorem in rows}
    files = source_lines(root)
    declarations = declaration_blocks(files, names)
    definitions = named_defs(files)

    results: list[dict[str, str]] = []
    for routine, theorem in rows:
        short = theorem.rsplit(".", 1)[-1]
        declaration = declarations.get(short)
        if declaration is None:
            results.append({
                "routine": routine, "theorem": theorem, "kind": "missing",
                "classification": "unresolved", "source": "-", "line": "-",
                "detail": "registry theorem declaration not found",
            })
            continue
        path, line, text = declaration
        direct = hits(text)
        for kind, _ in direct:
            results.append({
                "routine": routine, "theorem": theorem, "kind": kind,
                "classification": "candidate" if kind == "zero-region" else "review",
                "source": str(path.relative_to(root)), "line": str(line),
                "detail": "direct theorem declaration",
            })
        for name, source_name in EXPAND_NAMES.items():
            if not re.search(rf'\b{re.escape(name)}\b', text):
                continue
            definition = definitions.get(name)
            if definition is None:
                results.append({
                    "routine": routine, "theorem": theorem, "kind": "dependency",
                    "classification": "unresolved", "source": source_name, "line": "-",
                    "detail": f"{name} referenced but definition not found",
                })
                continue
            def_path, def_line, def_text = definition
            for kind, _ in hits(def_text):
                results.append({
                    "routine": routine, "theorem": theorem, "kind": kind,
                    "classification": "candidate" if kind == "zero-region" else "review",
                    "source": f"{def_path.relative_to(root)}:{def_line}",
                    "line": str(line), "detail": f"expanded dependency {name}",
                })

    # The required positive control: fail closed if the scan no longer sees
    # the known fixed scratch premise behind address_from_pubkey.
    positive = [row for row in results
                if row["theorem"] == "addressFromPubkey_spec_within"
                and row["kind"] == "zero-region"]
    if not positive:
        raise SystemExit("positive control missing: addressFromPubkey_spec_within/afpCallerPre")

    args.out.parent.mkdir(parents=True, exist_ok=True)
    fields = ("routine", "theorem", "kind", "classification", "source", "line", "detail")
    with args.out.open("w", newline="") as handle:
        handle.write("# schema=proven-premise-census-v1\n")
        handle.write(f"# registry_rows={len(rows)}\n")
        handle.write(f"# unique_theorems={len(names)}\n")
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(results)

    candidates = [row for row in results if row["classification"] == "candidate"]
    print(f"registry_rows={len(rows)} unique_theorems={len(names)} "
          f"candidate_rows={len(candidates)} out={args.out}")
    for row in candidates:
        print("\t".join(row[field] for field in fields))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
