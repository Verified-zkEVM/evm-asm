#!/usr/bin/env python3
"""spec-oracle.py — generate a spec-correspondence oracle corpus.

Runs a pinned external reference over a deterministic corpus and writes the
committed TSV that `lake exe correspondence-check <family>` replays. See
docs/agents/spec-correspondence.md for the method, and `scripts/spec_oracle/`
for the shared mechanics.

Usage:
    scripts/spec-oracle.py --family rlp --out tests/correspondence/rlp.tsv
    scripts/spec-oracle.py --family rlp --check tests/correspondence/rlp.tsv

Adding a family: write `scripts/oracles/<name>.py` exporting a `FAMILY`, then
add it to REGISTRY below.
"""

import pathlib
import sys

# Same sys.path idiom the other multi-module scripts use (see gen-port-kit.py).
SCRIPTS = pathlib.Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import spec_oracle  # noqa: E402
from oracles import bal as bal_family  # noqa: E402
from oracles import header as header_family  # noqa: E402
from oracles import rlp as rlp_family  # noqa: E402

REGISTRY = [rlp_family.FAMILY, bal_family.FAMILY, header_family.FAMILY]

if __name__ == "__main__":
    raise SystemExit(spec_oracle.main(REGISTRY))
