"""oracles.rlp — the RLP family for the spec-correspondence oracle.

Reference: `ethereum_rlp`, the RLP implementation execution-specs depends on.
It is an **external** package (not vendored), so this family needs the version
pin machinery in `spec_oracle.pins`; a vendored-reference family does not.

Method: docs/agents/spec-correspondence.md
Findings: docs/rlp-spec-correspondence.md

Everything family-agnostic (TSV, pins, dedup, CLI, LCG) lives in `spec_oracle`.
This module supplies only the corpus and the oracle function.
"""

from __future__ import annotations

import pathlib
import sys

import spec_oracle
from spec_oracle import pins

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent.parent

try:
    from ethereum_rlp import rlp
    from ethereum_rlp.exceptions import RLPException
except ImportError:  # pragma: no cover - environment guard
    sys.stderr.write(
        "error: cannot import `ethereum_rlp`.\n"
        "It is an external PyPI package and is NOT vendored in this repo.\n"
        "Install the version pinned by execution-specs/uv.lock, e.g.:\n"
        "    uv pip install --target /tmp/rlp ethereum-rlp==0.1.6\n"
        "    PYTHONPATH=/tmp/rlp scripts/spec-oracle.py --family rlp ...\n"
    )
    raise SystemExit(2)


# --------------------------------------------------------------------------
# Corpus
# --------------------------------------------------------------------------

def boundary_cases() -> list[bytes]:
    """Hand-picked inputs pinning each canonicality rule and each side of the
    55/56 boundary. These are the cases the verdicts actually turn on, so they
    lead the corpus."""
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
        # All VALID byte strings at the decode layer, and the reference accepts
        # every one. The integer rules — reject a leading zero, reject overlong
        # for the target width — live one layer up in `_deserialize_to_uint`,
        # and differ per field type (Uint unbounded, U64 caps at 8 bytes, U256
        # at 32). Keeping these here makes that layer boundary explicit: a
        # divergence in the guest's *scalar* routines would NOT show up in this
        # corpus, which is why those rows are graded `insp` rather than `diff`.
        b"\x82\x00\x01",           # leading-zero content: valid bytes, non-canonical integer
        b"\x88" + b"\xff" * 8,     # 8-byte integer: fits U64
        b"\x89" + b"\xff" * 9,     # 9-byte integer: overflows U64, fine for Uint
        b"\xa0" + b"\xff" * 32,    # 32-byte integer: fits U256
        b"\xa1" + b"\xff" * 33,    # 33-byte integer: overflows U256, fine for Uint
    ]
    # A deep-nesting ladder: each level wraps the previous in a 1-item list.
    deep = b"\xc0"
    for _ in range(12):
        deep = bytes([0xC0 + len(deep)]) + deep
        cases.append(deep)
    return cases


def _random_value(gen, depth: int):
    """Build a random decoded-RLP value (nested lists of byte strings)."""
    if depth <= 0 or next(gen) % 3 == 0:
        return bytes((next(gen) % 256) for _ in range(next(gen) % 60))
    return [_random_value(gen, depth - 1) for _ in range(next(gen) % 4)]


def structured_cases(count: int, seed: int) -> list[bytes]:
    """Well-formed encodings, plus mutations of them.

    Purely random buffers are almost always rejected by both sides, so they only
    test agreement on *rejection*. These test the other half — that both sides
    accept the same inputs AND decode them to the same value — and the
    mutations sit near the valid/invalid boundary, which is where a strictness
    difference actually shows up."""
    gen = spec_oracle.lcg(seed)
    out: list[bytes] = []
    for _ in range(count):
        try:
            encoded = rlp.encode(_random_value(gen, depth=3))
        except RecursionError:
            continue
        out.append(encoded)
        if not encoded:
            continue
        # Mutate one byte, truncate, and extend — each probes a different rule
        # (header validity, truncation, trailing bytes).
        idx = next(gen) % len(encoded)
        mutated = bytearray(encoded)
        mutated[idx] = (mutated[idx] + 1 + next(gen) % 255) % 256
        out.append(bytes(mutated))
        out.append(encoded[:-1])
        out.append(encoded + b"\x00")
    return out


def random_cases(count: int, seed: int) -> list[bytes]:
    """Seeded random byte buffers. Most are rejected by both sides; their job is
    to catch a rule one side enforces and the other does not."""
    gen = spec_oracle.lcg(seed)
    out: list[bytes] = []
    for _ in range(count):
        length = next(gen) % 12
        out.append(bytes((next(gen) % 256) for _ in range(length)))
    return out


def corpus() -> list[bytes]:
    return boundary_cases() + structured_cases(600, seed=7) + random_cases(2000, seed=42)


# --------------------------------------------------------------------------
# Oracle
# --------------------------------------------------------------------------

def render(value) -> str:
    """Canonical S-expression rendering of a decoded RLP value.

    bytes -> "<hex>"; list -> (<item> ...). Chosen so the Lean side can emit an
    identical string from an `RLPItem` with no parser on either end.
    """
    if isinstance(value, (bytes, bytearray)):
        return '"' + bytes(value).hex() + '"'
    return "(" + " ".join(render(v) for v in value) + ")"


def oracle(data: bytes) -> tuple[str, str, str]:
    """(verdict, detail, aux). `aux` is the encoder direction: does re-encoding
    the decoded value reproduce the input exactly? That lets the Lean side check
    `EL.RLP.encode` against the reference without a second corpus."""
    try:
        decoded = rlp.decode(data)
    except RLPException as e:
        msg = str(e).split("\n")[0].strip()
        return ("reject", f"{type(e).__name__}:{msg}" if msg else type(e).__name__, "-")
    except RecursionError:
        # Not an RLPException: the reference has no depth limit and blows the
        # Python stack instead. Recorded distinctly because it is a behavioural
        # difference from a total decoder, not a decode verdict.
        return ("reject", "RecursionError", "-")
    try:
        aux = "same" if rlp.encode(decoded) == data else "differs"
    except (RLPException, RecursionError):
        aux = "error"
    return ("accept", render(decoded), aux)


FAMILY = spec_oracle.Family(
    name="rlp",
    corpus=corpus,
    oracle=oracle,
    reference=pins.ExternalPackage("ethereum-rlp", REPO_ROOT),
    aux_label="re-encode reproduces input",
)
