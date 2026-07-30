#!/usr/bin/env python3
"""rlp-python-oracle.py — generate the Python-side RLP oracle corpus.

Runs the *reference* RLP implementation used by execution-specs
(`ethereum_rlp`, pinned by `execution-specs/uv.lock`) over a deterministic
corpus of byte strings and records, for each one, whether the reference
accepts it and — when it does — the decoded value in a canonical textual
form. The result is written as a TSV that `lake exe rlp-oracle-check`
replays against `EvmAsm.EL.RLP.decodeFully`, so the correspondence claims in
`docs/rlp-ssz-spec-correspondence.md` are reproducible rather than asserted.

WHY A COMMITTED TSV: CI has no Python environment for execution-specs and no
network. Generating the oracle is a local step; the checked-in TSV is what CI
gates on. Regenerating must be byte-for-byte reproducible, hence: no RNG from
the `random` module (an explicit LCG instead), sorted output, fixed corpus.

Usage:
    scripts/rlp-python-oracle.py --out tests/rlp-vectors/python-oracle.tsv
    scripts/rlp-python-oracle.py --check tests/rlp-vectors/python-oracle.tsv

`--check` regenerates in memory and diffs against the file, so a stale TSV is
caught without writing.

The `ethereum_rlp` package must be importable. It is NOT vendored in this
repo (see the correspondence doc); install the pinned version with:
    uv pip install --target <dir> ethereum-rlp==0.1.6
and put <dir> on PYTHONPATH.

TSV columns (tab-separated, one record per line):
    input_hex <TAB> verdict <TAB> detail <TAB> reencode
where verdict is `accept` or `reject`; detail is the decoded value in
S-expression form for `accept`, and the reference's error class (plus its
message when it carries one) for `reject`; reencode is `same`/`differs`
(whether re-encoding the decoded value reproduces the input byte-for-byte),
or `-` when the input was rejected. The reencode column is what lets the
Lean side check `EL.RLP.encode` against the reference, not just the decoder.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys

try:
    from ethereum_rlp import rlp
    from ethereum_rlp.exceptions import RLPException
except ImportError:  # pragma: no cover - environment guard
    sys.stderr.write(
        "error: cannot import `ethereum_rlp`.\n"
        "It is an external PyPI package and is NOT vendored in this repo.\n"
        "Install the version pinned by execution-specs/uv.lock:\n"
        "    uv pip install --target /tmp/rlp ethereum-rlp==0.1.6\n"
        "    PYTHONPATH=/tmp/rlp scripts/rlp-python-oracle.py ...\n"
    )
    raise SystemExit(2)


# --------------------------------------------------------------------------
# Corpus
# --------------------------------------------------------------------------

def _lcg(seed: int):
    """Deterministic LCG (glibc constants). Mirrors the generator style in
    EvmAsm/Tests/RlpDiffCheck.lean so both sides stay reproducible.

    Yields the HIGH bits (state >> 15), not the raw state: the low bits of a
    power-of-two-modulus LCG have periods as short as 2 (bit 0 alternates),
    so `state % 256` produces a handful of distinct byte patterns and the
    corpus collapses under dedup. Taking the high bits restores the full
    period."""
    state = seed
    while True:
        state = (state * 1103515245 + 12345) & 0x7FFFFFFF
        yield state >> 15


def boundary_cases() -> list[bytes]:
    """Hand-picked inputs that pin each canonicality rule and each side of the
    55/56 boundary. These are the cases the correspondence table's verdicts
    actually turn on, so they lead the corpus."""
    cases: list[bytes] = [
        b"",                       # empty input
        b"\x00",                   # single zero byte
        b"\x01",                   # single byte, canonical
        b"\x7f",                   # single byte, top of the bare range
        b"\x80",                   # empty string
        b"\x81\x00",               # non-canonical: 0x00 should be bare
        b"\x81\x7f",               # non-canonical: 0x7f should be bare
        b"\x81\x80",               # canonical: 0x80 needs the wrapper
        b"\x82\x01",               # truncated short string
        b"\x82\x01\x02",           # well-formed 2-byte string
        b"\x82\x01\x02\xff",       # trailing byte after a complete item
        b"\xb7" + b"\x61" * 55,    # short form at the 55 boundary
        b"\xb8\x37" + b"a" * 55,   # long form declaring 55 -> non-minimal
        b"\xb8\x38" + b"a" * 56,   # long form declaring 56 -> minimal, valid
        b"\xb8\x00",               # long form, zero length
        b"\xb8\x01\x61",           # long form declaring 1 -> non-minimal
        b"\xb9\x00\x38" + b"a" * 56,   # leading zero in the length field
        b"\xb9\x01\x00" + b"a" * 256,  # 2-byte length, valid
        b"\xb8\x38" + b"a" * 55,   # long form, truncated payload
        b"\xbf" + b"\x01" * 8,     # 8-byte length header, truncated
        b"\xc0",                   # empty list
        b"\xc1\x00",               # list containing a single zero byte
        b"\xc2\x01\x02",           # list of two single bytes
        b"\xc1\x81\x00",           # list containing a non-canonical item
        b"\xc2\x01",               # truncated list payload
        b"\xc0\xff",               # trailing byte after a complete list
        b"\xc8" + b"\x01" * 8,     # short list, 8 items
        b"\xf7" + b"\x01" * 55,    # short list at the 55 boundary
        b"\xf8\x37" + b"\x01" * 55,    # long list declaring 55 -> non-minimal
        b"\xf8\x38" + b"\x01" * 56,    # long list declaring 56 -> minimal
        b"\xf9\x00\x38" + b"\x01" * 56,  # leading zero in list length
        b"\xc1\xc0",               # nested empty list
        b"\xc3\xc2\xc1\xc0",       # nesting depth 4
        b"\xff",                   # max prefix, no length bytes
        b"\xf8",                   # long-list prefix, nothing follows
        b"\xb8",                   # long-string prefix, nothing follows

        # --- Integer-shaped payloads -------------------------------------
        # These are all VALID byte strings at the decode layer, and the
        # reference accepts every one of them. The integer rules — reject a
        # leading zero, reject overlong for the target width — live one layer
        # up, in `_deserialize_to_uint`, and differ per field type
        # (Uint is unbounded, U64 caps at 8 bytes, U256 at 32). Keeping these
        # in the corpus makes that layer boundary explicit: a divergence in
        # our *scalar* routines would NOT show up here, which is why the
        # number rows in the correspondence doc are marked `insp`.
        b"\x82\x00\x01",           # leading-zero content: valid bytes, non-canonical integer
        b"\x88" + b"\xff" * 8,     # 8-byte integer: fits U64
        b"\x89" + b"\xff" * 9,     # 9-byte integer: overflows U64, fine for Uint
        b"\xa0" + b"\xff" * 32,    # 32-byte integer: fits U256
        b"\xa1" + b"\xff" * 33,    # 33-byte integer: overflows U256, fine for Uint
        b"\x81\x00",               # single zero byte, wrapped (non-canonical both layers)
    ]
    # A deep-nesting ladder: each level wraps the previous in a 1-item list.
    deep = b"\xc0"
    for _ in range(12):
        deep = bytes([0xC0 + len(deep)]) + deep
        cases.append(deep)
    return cases


def random_cases(count: int, seed: int) -> list[bytes]:
    """Seeded random byte buffers. Most are rejected by both sides; their job
    is to catch a rule one side enforces and the other does not."""
    gen = _lcg(seed)
    out: list[bytes] = []
    for _ in range(count):
        length = next(gen) % 12
        buf = bytearray()
        for _ in range(length):
            # Bias the first byte toward structural prefixes so the corpus
            # exercises headers rather than mostly-bare single bytes.
            buf.append(next(gen) % 256)
        out.append(bytes(buf))
    return out


def _random_value(gen, depth: int):
    """Build a random decoded-RLP value (nested lists of byte strings)."""
    if depth <= 0 or next(gen) % 3 == 0:
        return bytes((next(gen) % 256) for _ in range(next(gen) % 60))
    return [_random_value(gen, depth - 1) for _ in range(next(gen) % 4)]


def structured_cases(count: int, seed: int) -> list[bytes]:
    """Well-formed encodings, plus single-byte mutations of them.

    Purely random buffers are almost always rejected by both sides, so they
    only test agreement on *rejection*. These cases test the other half: that
    both sides accept the same inputs AND decode them to the same value. The
    mutations sit near the valid/invalid boundary, which is where a strictness
    difference actually shows up."""
    gen = _lcg(seed)
    out: list[bytes] = []
    for _ in range(count):
        try:
            encoded = rlp.encode(_random_value(gen, depth=3))
        except RecursionError:
            continue
        out.append(encoded)
        if not encoded:
            continue
        # Mutate one byte, and truncate, and extend — each probes a different
        # rule (header validity, truncation, trailing bytes).
        idx = next(gen) % len(encoded)
        mutated = bytearray(encoded)
        mutated[idx] = (mutated[idx] + 1 + next(gen) % 255) % 256
        out.append(bytes(mutated))
        out.append(encoded[:-1])
        out.append(encoded + b"\x00")
    return out


def corpus() -> list[bytes]:
    seen: set[bytes] = set()
    out: list[bytes] = []
    for b in (boundary_cases()
              + structured_cases(600, seed=7)
              + random_cases(2000, seed=42)):
        if b not in seen:
            seen.add(b)
            out.append(b)
    return out


# --------------------------------------------------------------------------
# Oracle
# --------------------------------------------------------------------------

def render(value) -> str:
    """Canonical S-expression rendering of a decoded RLP value.

    bytes  -> "<hex>"      (empty bytes render as "")
    list   -> (<item> ...)  (empty list renders as ())
    Chosen so the Lean side can emit an identical string from an `RLPItem`
    without needing a parser on either end.
    """
    if isinstance(value, (bytes, bytearray)):
        return '"' + bytes(value).hex() + '"'
    return "(" + " ".join(render(v) for v in value) + ")"


def oracle(data: bytes) -> tuple[str, str, str]:
    """Returns (verdict, detail, reencode).

    `reencode` covers the *encoder* direction: whether re-encoding the decoded
    value reproduces the input exactly. It is `same` for a canonical encoding
    and `differs` otherwise, and lets the Lean side check `EL.RLP.encode`
    against the reference without a second corpus. `-` when undecodable."""
    try:
        decoded = rlp.decode(data)
    except RLPException as e:
        msg = str(e).split("\n")[0].strip()
        return ("reject", f"{type(e).__name__}:{msg}" if msg else type(e).__name__, "-")
    except RecursionError:
        # Not an RLPException: the reference has no depth limit and blows the
        # Python stack instead. Recorded distinctly because it is a genuine
        # behavioural difference from a total decoder, not a decode verdict.
        return ("reject", "RecursionError", "-")
    try:
        reencode = "same" if rlp.encode(decoded) == data else "differs"
    except (RLPException, RecursionError):
        reencode = "error"
    return ("accept", render(decoded), reencode)


def generate() -> list[str]:
    lines = []
    for data in corpus():
        verdict, detail, reencode = oracle(data)
        lines.append(f"{data.hex()}\t{verdict}\t{detail}\t{reencode}")
    return lines


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
UV_LOCK = REPO_ROOT / "execution-specs" / "uv.lock"


def locked_rlp_version() -> str | None:
    """The `ethereum-rlp` version pinned by execution-specs/uv.lock.

    `None` when the submodule is not populated. The uv.lock `[[package]]`
    blocks are name/version pairs; we want the version line that follows
    `name = "ethereum-rlp"` in the same block."""
    if not UV_LOCK.exists():
        return None
    text = UV_LOCK.read_text(encoding="utf-8")
    m = re.search(r'^name = "ethereum-rlp"\nversion = "([^"]+)"',
                  text, re.MULTILINE)
    return m.group(1) if m else None


def installed_rlp_version() -> str:
    from importlib.metadata import version
    return version("ethereum-rlp")


def execution_specs_sha() -> str:
    """The execution-specs gitlink SHA recorded in the superproject tree.

    Read from the tree, not the submodule working copy, so it is available
    even when the submodule is not checked out — which is how CI verifies the
    committed corpus still describes the pinned reference."""
    out = subprocess.run(
        ["git", "ls-tree", "HEAD", "execution-specs"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True).stdout
    m = re.search(r"commit ([0-9a-f]{40})", out)
    return m.group(1) if m else "unknown"


def check_pins() -> str:
    """Refuse to generate against a reference that is not the pinned one.

    This is the generator half of the staleness guard: it makes producing a
    wrong-version corpus impossible rather than merely detectable."""
    installed = installed_rlp_version()
    locked = locked_rlp_version()
    if locked is None:
        sys.stderr.write(
            "error: execution-specs/uv.lock not found — the submodule is not "
            "populated, so the pin cannot be verified.\n"
            "  git submodule update --init execution-specs\n"
        )
        raise SystemExit(2)
    if installed != locked:
        sys.stderr.write(
            f"error: installed ethereum-rlp {installed} != pinned {locked} "
            f"(execution-specs/uv.lock).\n"
            f"Generating against the wrong reference would make the oracle "
            f"silently authoritative for a version this repo does not use.\n"
            f"  uv pip install --target <dir> ethereum-rlp=={locked}\n"
        )
        raise SystemExit(2)
    return installed


def header(rlp_version: str) -> list[str]:
    return [
        "# Generated by scripts/rlp-python-oracle.py — DO NOT EDIT BY HAND.",
        "# Oracle: ethereum_rlp (external PyPI package, NOT vendored).",
        # The two stamps below are what makes staleness detectable. The
        # gitlink SHA is readable in CI WITHOUT the submodule checked out, so
        # `lake exe rlp-oracle-check` can tell that execution-specs moved and
        # this corpus was never re-validated against the new pin.
        f"# oracle-version: ethereum-rlp=={rlp_version}",
        f"# execution-specs: {execution_specs_sha()}",
        "# Columns: input_hex <TAB> accept|reject <TAB> detail <TAB> reencode",
        "#   detail   = S-expression of the decoded value, or ErrorClass:message.",
        "#   reencode = same|differs (does re-encoding reproduce the input?), - if rejected.",
    ]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=pathlib.Path, help="write the TSV here")
    ap.add_argument("--check", type=pathlib.Path,
                    help="verify an existing TSV is up to date; write nothing")
    args = ap.parse_args()

    rlp_version = check_pins()
    body = generate()
    text = "\n".join(header(rlp_version) + body) + "\n"

    if args.check:
        existing = args.check.read_text(encoding="utf-8")
        if existing != text:
            sys.stderr.write(
                f"error: {args.check} is stale — regenerate with\n"
                f"    scripts/rlp-python-oracle.py --out {args.check}\n"
            )
            return 1
        print(f"{args.check}: up to date ({len(body)} records)")
        return 0

    if not args.out:
        ap.error("one of --out or --check is required")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(text, encoding="utf-8")
    accepts = sum(1 for line in body if "\taccept\t" in line)
    print(f"wrote {args.out}: {len(body)} records "
          f"({accepts} accept, {len(body) - accepts} reject)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
