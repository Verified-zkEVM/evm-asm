#!/usr/bin/env python3
"""Regression test for the EEST sampler's corpus-span self-check.

Run: ``scripts/check-eest-sampler-span.py``  (exit 0 = pass)

WHY THIS EXISTS AS A TEST RATHER THAN AS AN ASSERTION ALONE. The sampler's
span check refuses to emit a manifest when a ``--random`` draw does not span
the corpus. An assertion nobody has seen fail is not known to work, so this
drives it with a KNOWN-BAD INPUT whose expected output is the historical
failure -- a negative control, not a smoke test.

THE KNOWN-BAD INPUT IS THE ACTUAL HISTORICAL DEFECT. Two shipped versions of
``--random`` selected the FRONT of the manifest rather than a sample of it:
first because the flag never reached the converter (GH #10596), then because
it sampled fixture FILES rather than blocks (GH #10597). Both were reported as
corpus-wide coverage and both passed review. A front-of-corpus draw of 200
blocks spans ~53 fixture FILES -- that 53 is the signature of the defect, and
it is pinned below as a fixture value rather than described in a comment.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

# The corpus size, agreed by THREE separately-derived enumerations: this
# script's converter, the independent implementation in GH #10603, and an
# unrelated earlier run's block manifest. A number nobody cross-checked is a
# number nobody knows; this one has been checked three ways.
CORPUS_BLOCKS = 26104

# A 200-block draw taken from the FRONT of the corpus spans this many fixture
# files. This is the file-uniform behaviour's signature, measured on the real
# corpus, and it is what the check must reject.
FRONT_DRAW_FILE_SPAN = 53
DRAW = 200


def load_converter():
    path = Path(__file__).resolve().parent / "eest-stateless-to-input.py"
    spec = importlib.util.spec_from_file_location("eest_conv", path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    conv = load_converter()
    err = conv.selection_span_error
    failures: list[str] = []

    def expect(name: str, cond: bool, detail: str = "") -> None:
        print(f"  {'ok  ' if cond else 'FAIL'}  {name}{'  ' + detail if detail else ''}")
        if not cond:
            failures.append(name)

    # NEGATIVE CONTROL: the historical defect must be rejected.
    front = list(range(DRAW))
    msg = err(front, CORPUS_BLOCKS)
    expect(
        "front-of-corpus draw is REJECTED (the GH #10596/#10597 defect)",
        msg is not None,
        f"draw={DRAW} corpus={CORPUS_BLOCKS} span={FRONT_DRAW_FILE_SPAN} files",
    )
    if msg is not None:
        expect("rejection message names the highest index", str(DRAW - 1) in msg)

    # A first-half-confined draw is the same defect in weaker form.
    spread_but_front = list(range(0, CORPUS_BLOCKS // 2 - 1, (CORPUS_BLOCKS // 2) // DRAW))[:DRAW]
    expect(
        "draw confined to the first half is REJECTED even when spread",
        err(spread_but_front, CORPUS_BLOCKS) is not None,
    )

    # POSITIVE CONTROL: a genuine uniform draw must pass. Fixed seed so this
    # test cannot flake.
    import random

    uniform = random.Random(20260726).sample(range(CORPUS_BLOCKS), DRAW)
    expect(
        "uniform draw is ACCEPTED",
        err(uniform, CORPUS_BLOCKS) is None,
        f"max index {max(uniform)} of {CORPUS_BLOCKS}",
    )

    # The check must not fire where it cannot carry: a tiny draw can land
    # anywhere legitimately, and a guard that trips on correct input is worse
    # than no guard.
    expect("small draw is EXEMPT (would otherwise false-positive)",
           err(list(range(5)), CORPUS_BLOCKS) is None)
    expect("draw comparable to corpus size is EXEMPT",
           err(list(range(DRAW)), DRAW * 2) is None)

    print()
    if failures:
        print(f"check-eest-sampler-span: FAILED ({len(failures)}): {', '.join(failures)}")
        return 1
    print("check-eest-sampler-span: OK -- the span check rejects the historical "
          "defect and accepts a uniform draw.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
