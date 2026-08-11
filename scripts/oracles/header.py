#!/usr/bin/env python3
"""Header family: guest RLP header decode vs the vendored ``_decode_header``.

Reference: ``ethereum.forks.amsterdam.stateless._decode_header``
(execution-specs/src/ethereum/forks/amsterdam/stateless.py), the *vendored*
implementation pinned by the submodule gitlink — the exact counterpart of the
Lean model ``SpecRef._decode_header`` (EvmAsm/Stateless/SpecRef/Stateless.lean),
including the 23-field current-fork vs 21-field previous-fork dispatch.

Verdict: accept iff ``_decode_header`` returns.  Detail: the decoded header
rendered as ``(header current|previous <fields...>)`` with byte fields as
quoted hex and numeric fields as decimal, so a value divergence is locatable.
Aux: re-encoding the decoded value reproduces the input (the reference encode
side is unconditional on the accepting path, mirroring
``SpecRef.BlocksRlp.headerToRlpItem``).

Corpus: boundary cases cover both fork arms, the field-count boundary
(20/22/24 fields), overlong U64/U256 scalars, wrong FixedBytes widths,
trailing bytes, non-list top level, nested lists, non-canonical length
prefixes, and leading-zero scalars — the GH #11986 class: a confirmed
false-accept lived exactly there (non-canonical integer accepted by the
guest's transaction decode), so a boundary case is chosen *because* a real
false accept lived at that boundary, not for generic completeness.  Structured
cases encode random headers and then mutate them (byte flip / truncation /
extension); random cases are raw byte strings.
"""

from __future__ import annotations

import dataclasses
import pathlib
import sys
from typing import Iterator

from ethereum_rlp import rlp
from ethereum_types.numeric import U64, U256, Uint

from spec_oracle import Family, lcg
from spec_oracle import pins

_AMSTERDAM = (
    pathlib.Path(__file__).resolve().parent.parent.parent / "execution-specs" / "src"
)
if str(_AMSTERDAM) not in sys.path:
    sys.path.insert(0, str(_AMSTERDAM))

from ethereum.forks.amsterdam import blocks, stateless  # noqa: E402
from ethereum.forks.bpo5 import blocks as _bpo5_blocks  # noqa: E402

_B32 = bytes(32)
_B20 = bytes(20)
_B8 = bytes(8)


def _header(**overrides) -> blocks.Header:
    fields = dict(
        parent_hash=_B32,
        ommers_hash=_B32,
        coinbase=_B20,
        state_root=_B32,
        transactions_root=_B32,
        receipt_root=_B32,
        bloom=bytes(256),
        difficulty=Uint(0),
        number=U64(1),
        gas_limit=U64(30_000_000),
        gas_used=U64(0),
        timestamp=U64(1),
        extra_data=b"",
        prev_randao=_B32,
        nonce=_B8,
        base_fee_per_gas=U256(7),
        withdrawals_root=_B32,
        blob_gas_used=U64(0),
        excess_blob_gas=U64(0),
        parent_beacon_block_root=_B32,
        requests_hash=_B32,
        block_access_list_hash=_B32,
        slot_number=U64(1),
    )
    fields.update(overrides)
    for name, ty in (
        ("difficulty", Uint),
        ("number", U64),
        ("gas_limit", U64),
        ("gas_used", U64),
        ("timestamp", U64),
        ("base_fee_per_gas", U256),
        ("blob_gas_used", U64),
        ("excess_blob_gas", U64),
        ("slot_number", U64),
    ):
        fields[name] = ty(fields[name])
    return blocks.Header(**fields)


def _previous(h: blocks.Header) -> blocks.PreviousForkHeader:
    d = {f.name: getattr(h, f.name) for f in dataclasses.fields(h)}
    del d["block_access_list_hash"]
    del d["slot_number"]
    return _bpo5_blocks.Header(**d)


def _render(h) -> str:
    tag = "current" if isinstance(h, blocks.Header) else "previous"
    parts = []
    for f in dataclasses.fields(h):
        v = getattr(h, f.name)
        if isinstance(v, (bytes, bytearray)):
            parts.append(f'"{bytes(v).hex()}"')
        else:
            parts.append(str(int(v)))
    return f"(header {tag} {' '.join(parts)})"


def oracle(data: bytes):
    try:
        h = stateless._decode_header(data)
    except rlp.DecodingError as exc:
        return ("reject", f"DecodingError:{exc}", "-")
    aux = "same" if bytes(rlp.encode(h)) == data else "differs"
    return ("accept", _render(h), aux)


def _random_header(gen) -> blocks.Header:
    rb = lambda n: bytes(next(gen) % 256 for _ in range(n))  # noqa: E731
    return _header(
        parent_hash=rb(32),
        state_root=rb(32),
        coinbase=rb(20),
        transactions_root=rb(32),
        receipt_root=rb(32),
        bloom=rb(256),
        number=next(gen) % 10_000_000,
        gas_limit=1_000_000 + next(gen) % 100_000_000,
        gas_used=next(gen) % 30_000_000,
        timestamp=1_700_000_000 + next(gen) % 100_000_000,
        extra_data=rb(next(gen) % 33),
        prev_randao=rb(32),
        base_fee_per_gas=next(gen) % 10_000,
        withdrawals_root=rb(32),
        blob_gas_used=next(gen) % 786_432,
        excess_blob_gas=next(gen) % 786_432,
        parent_beacon_block_root=rb(32),
        requests_hash=rb(32),
        block_access_list_hash=rb(32),
        slot_number=next(gen) % 10_000_000,
    )


def _wrap(payload: bytes) -> bytes:
    """RLP list wrapper for an already-encoded payload."""
    if len(payload) <= 55:
        return bytes([0xC0 + len(payload)]) + payload
    if len(payload) <= 255:
        return b"\xf8" + bytes([len(payload)]) + payload
    lb = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([0xF7 + len(lb)]) + lb + payload


def boundary_cases() -> Iterator[bytes]:
    valid = bytes(rlp.encode(_header()))
    prev = bytes(rlp.encode(_previous(_header())))
    yield valid
    yield prev
    yield bytes(rlp.encode(_header(number=2**64 - 1, slot_number=2**64 - 1)))
    yield bytes(rlp.encode(_header(base_fee_per_gas=2**256 - 1)))
    yield bytes(rlp.encode(_header(gas_limit=0, extra_data=bytes(32))))
    # Leading-zero scalar — GH #11986 class: a confirmed false accept lived
    # exactly at the non-canonical-integer boundary.  Replace the encoded
    # `number` field (0x01, the fourth scalar after three 32-byte hashes plus
    # the coinbase — locate it structurally instead) with a 2-byte encoding
    # whose content starts with a zero byte.
    items = list(rlp.decode(valid))
    items[8] = b"\x00\x01"  # number, non-canonical
    payload = b"".join(rlp.encode(i) for i in items)
    yield _wrap(payload)
    # Overlong scalars: the width gate binds only U64/U256 — Uint fields are
    # unbounded.  9-byte blob_gas_used (U64) and 33-byte timestamp (U256)
    # must reject; a 33-byte gas_limit (Uint) is legal and must accept.
    items[17] = b"\x01" + bytes(8)  # blob_gas_used: U64, 9 bytes
    yield _wrap(b"".join(rlp.encode(i) for i in items))
    items = list(rlp.decode(valid))
    items[11] = b"\x01" + bytes(32)  # timestamp: U256, 33 bytes
    yield _wrap(b"".join(rlp.encode(i) for i in items))
    items = list(rlp.decode(valid))
    items[9] = b"\x01" + bytes(32)  # gas_limit: Uint, 33 bytes — legal
    yield _wrap(b"".join(rlp.encode(i) for i in items))
    # Wrong FixedBytes widths.
    items = list(rlp.decode(valid))
    items[0] = bytes(31)  # parent_hash short
    yield _wrap(b"".join(rlp.encode(i) for i in items))
    items[0] = bytes(33)  # parent_hash long
    yield _wrap(b"".join(rlp.encode(i) for i in items))
    # Field-count boundary: 20, 22, 24 fields (21 and 23 are the legal arms).
    items = list(rlp.decode(valid))
    yield _wrap(b"".join(rlp.encode(i) for i in items[:20]))
    yield _wrap(b"".join(rlp.encode(i) for i in items[:22]))
    yield _wrap(b"".join(rlp.encode(i) for i in items + [b"\x00"]))
    # Trailing bytes after a complete item.
    yield valid + b"\x00"
    yield valid + valid
    # Top level is not a list; a field is a nested list.
    yield bytes(rlp.encode(b"\x01" * 32))
    items = list(rlp.decode(valid))
    items[3] = [b"\x01"]
    yield _wrap(b"".join(rlp.encode(i) for i in items))
    # Non-canonical list wrapper: long form for a short payload.
    short = bytes(rlp.encode([b"\x01"]))
    payload = short[1:]
    yield b"\xf8" + bytes([len(payload)]) + payload
    # Empty input and bare wrappers.
    yield b""
    yield b"\xc0"
    yield b"\xf8\x00"


def structured_cases(count: int, seed: int) -> Iterator[bytes]:
    gen = lcg(seed)
    emitted = 0
    while emitted < count:
        h = _random_header(gen)
        if next(gen) % 8 == 0:
            data = bytes(rlp.encode(_previous(h)))
        else:
            data = bytes(rlp.encode(h))
        yield data
        emitted += 1
        if emitted >= count:
            break
        m = bytearray(data)
        which = next(gen) % 3
        if which == 0:
            m[next(gen) % len(m)] ^= 1 + next(gen) % 255
        elif which == 1:
            m = m[: 1 + next(gen) % (len(m) - 1)]
        else:
            m.extend(bytes(1 + next(gen) % 8))
        yield bytes(m)
        emitted += 1


def random_cases(count: int, seed: int) -> Iterator[bytes]:
    gen = lcg(seed)
    for _ in range(count):
        n = next(gen) % 128
        yield bytes(next(gen) % 256 for _ in range(n))
        if n % 3 == 0:
            yield bytes([0xC0 | (next(gen) % 64)]) + bytes(
                next(gen) % 256 for _ in range(next(gen) % 16)
            )


def corpus() -> Iterator[bytes]:
    yield from boundary_cases()
    yield from structured_cases(200, seed=13)
    yield from random_cases(400, seed=17)


FAMILY = Family(
    name="header",
    corpus=corpus,
    oracle=oracle,
    reference=pins.Vendored(
        "src/ethereum/forks/amsterdam/stateless.py",
        _AMSTERDAM.parent.parent,
    ),
)
