#!/usr/bin/env python3
"""Detect self-contained dead codegen probe programs.

A "probe program" is one of the block_number / block_hash historical-state
extractors in EvmAsm/Codegen/Programs/.  Each lives in a single file and, for a
single module stem ``S``, defines three RISC-V assembly-string constants:

    <stem-lc>Function          # the emitted assembly string
    zisk<S>Prologue            # zisk build-unit prologue wrapper
    zisk<S>DataSection          # the probe data section

The Function def and the two zisk wrappers differ only in the case of the first
letter of the module stem (e.g. `txCalculateTotalBlobGasFunction` vs
`ziskTxCalculateTotalBlobGas...`), which is why the family is recognised by
matching the stems, not by stringifying a single stem twice.

When the probe runner that used to link these into a `zisk*` BuildUnit is gone
(some such runners have been removed in a series of dead-code-removal PRs), the
three strings become unreferenced deadweight.  This script flags modules that
still DEFINE all three but are referenced by no other file.

HOW DEADNESS IS ESTABLISHED (and what it does NOT claim)
========================================================
For each `zisk<Stem>Prologue` the corresponding `zisk<Stem>DataSection` and the
`<stem-lc>Function` are derived, and the module is reported only when all three
tokens appear in exactly this one file.  Mentions-equals-one is a *sufficient*
condition for "no other file spells out these symbols", so self-containment is a
necessary part of the verdict; the family match (all three names share a stem)
keeps unrelated symbols in the same module from matching.

It is not a proof.  A symbol reached only through an `import
EvmAsm.Codegen.Programs.<Name>` alias whose *identifiers* are never written out
elsewhere would still pass this filter, and mentions counts tokens found in
comments/docstrings too.  Deadness therefore still needs the independent
`git grep -l <Name>` check that the reviewer applies (defining-file excluded,
prose filtered out): the mention filter is a fast pre-pass, not the evidence.
Cone/mention membership is an upper bound, exactly as noted in
scripts/import-graph-metrics.py.

Unlike a naive "file has exactly three defs" test, an internal helper `def`
(e.g. `def calculate_total_blob_gas(tx) -> U64:` inside the module) does not
disqualify it: membership is decided by the family match plus self-containment.

Use as:

    python3 scripts/scan_deadprobes.py

which prints one `EvmAsm/Codegen/Programs/<Name>.lean` per dead module.
"""
from __future__ import annotations

import os
import re
from collections import defaultdict

ROOT = "EvmAsm"
_FUNC = "Function"
_PROLOGUE = "Prologue"
_DATA = "DataSection"
_ZISK = "zisk"


def find_lean_files(root: str) -> list[str]:
    out: list[str] = []
    for dp, _dn, fns in os.walk(root):
        for f in fns:
            if f.endswith(".lean"):
                out.append(os.path.join(dp, f))
    return out


def tokens(text: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", text))


def def_names(text: str) -> set[str]:
    """Symbols this file actually *defines* (via a `def`), not merely mentions."""
    names: set[str] = set()
    for line in text.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("def ") or stripped.startswith("def\t"):
            name = stripped[4:].split()[0]
            names.add(name)
    return names


def main() -> None:
    files = find_lean_files(ROOT)
    text = {p: open(p, encoding="utf-8").read() for p in files}

    mentions: dict[str, set[str]] = defaultdict(set)
    for p in files:
        for t in tokens(text[p]):
            mentions[t].add(p)

    for p in sorted(files):
        defs = def_names(text[p])
        # Airtight per-file deadness (the reviewer's `git grep -l` method):
        # every symbol this file defines must be referenced only inside itself.
        # A live module is excluded the moment any def is spelled out elsewhere;
        # a dead module that happens to carry an *alive* sibling family is
        # likewise excluded, so this never reports a still-linked file.
        if not all(mentions[d] == {p} for d in defs):
            continue
        fns = {d for d in defs if d.endswith(_FUNC)}
        proqs = {d for d in defs if d.endswith(_PROLOGUE)}
        dsecs = {d for d in defs if d.endswith(_DATA)}

        for pr in proqs:
            if not pr.startswith(_ZISK):
                continue
            stem = pr[len(_ZISK):-len(_PROLOGUE)]
            dsection = f"{_ZISK}{stem}{_DATA}"
            if dsection not in dsecs:
                continue
            fn = stem[0].lower() + stem[1:] + _FUNC
            if fn not in fns:
                continue
            print(p)
            break


if __name__ == "__main__":
    main()
