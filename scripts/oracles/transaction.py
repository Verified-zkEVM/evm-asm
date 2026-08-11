#!/usr/bin/env python3
"""transaction.py — spec-oracle family: transaction envelope decode (GH #11570 PR2).

Oracle:  ``ethereum.forks.amsterdam.transactions.decode_transaction``
         (vendored execution-specs, pinned by the submodule gitlink).
Subject: ``SpecRef.Transactions.decode_transaction``
         (EvmAsm/Stateless/SpecRef/Transactions.lean).

This is the valuable family of the #11570 sequence: the GH #11986 FA class
(non-canonical integer accepted at the attacker boundary) lives here — the
corpus's leading-zero-scalar cases name it explicitly.

Wire format: hex bytes (default ``render_input``).  Rejections compare
verdict only (harness contract); acceptances compare the full rendered
transaction plus the re-encode aux.

REGENERATION ENVIRONMENT (mandatory): the corpus must be regenerated in an
environment synced from ``execution-specs/uv.lock`` — ethereum_rlp /
ethereum_types versions move strictness verdicts (measured in #11570 PR1).

    python3 scripts/spec-oracle.py --family transaction \
        --out tests/correspondence/transaction.tsv
"""

from __future__ import annotations

import dataclasses
import os
import pathlib
import sys
from typing import Iterable, Tuple

_REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
_AMSTERDAM = os.path.join(
    _REPO_ROOT, "execution-specs", "src", "ethereum", "forks", "amsterdam"
)
if _AMSTERDAM not in sys.path:
    sys.path.insert(0, _AMSTERDAM)

from spec_oracle import Family, lcg  # noqa: E402
from spec_oracle import pins  # noqa: E402

from ethereum_rlp import rlp  # noqa: E402
from ethereum_types.bytes import Bytes, Bytes20, Bytes32  # noqa: E402
from ethereum_types.numeric import U64, U256, Uint  # noqa: E402

from ethereum.forks.amsterdam import transactions as _txs  # noqa: E402
from ethereum.forks.amsterdam.exceptions import TransactionTypeError  # noqa: E402
from ethereum.forks.amsterdam.fork_types import Authorization  # noqa: E402

LegacyTransaction = _txs.LegacyTransaction
Access = _txs.Access
AccessListTransaction = _txs.AccessListTransaction
FeeMarketTransaction = _txs.FeeMarketTransaction
BlobTransaction = _txs.BlobTransaction
SetCodeTransaction = _txs.SetCodeTransaction

# ---------------------------------------------------------------------------
# oracle
# ---------------------------------------------------------------------------

_REJECT_EXCEPTIONS = (
    rlp.DecodingError,
    TransactionTypeError,
    IndexError,      # empty input: tx[0]
    AssertionError,  # 0xFF: tx[0] >= 0xC0 asserts <= 0xFE
)


def oracle(data: bytes) -> Tuple[str, str, str]:
    """(verdict, detail, aux).  detail = rendered transaction; aux =
    'same' iff re-encoding the decoded transaction reproduces the input."""
    try:
        decoded = _txs.decode_transaction(Bytes(data))
    except _REJECT_EXCEPTIONS as e:
        return ("reject", f"{type(e).__name__}:{e}", "-")
    detail = render_tx(decoded)
    reenc = (
        rlp.encode(decoded)
        if isinstance(decoded, LegacyTransaction)
        else _txs.encode_transaction(decoded)
    )
    return ("accept", detail, "same" if bytes(reenc) == data else "differs")


# ---------------------------------------------------------------------------
# rendering (mirrored by the Lean subject — keep grammars in sync)
# ---------------------------------------------------------------------------

_TAGS = {
    LegacyTransaction: "legacy",
    AccessListTransaction: "access-list",
    FeeMarketTransaction: "fee-market",
    BlobTransaction: "blob",
    SetCodeTransaction: "set-code",
}


def render_value(v) -> str:
    if isinstance(v, bytes):
        return f'"{v.hex()}"'
    if dataclasses.is_dataclass(v) and not isinstance(v, type):
        inner = " ".join(render_value(getattr(v, f.name))
                         for f in dataclasses.fields(v))
        return f"({inner})"
    if isinstance(v, (list, tuple)):
        return "(" + " ".join(render_value(x) for x in v) + ")"
    return str(int(v))


def render_tx(tx) -> str:
    fields = " ".join(render_value(getattr(tx, f.name))
                      for f in dataclasses.fields(tx))
    return f"(tx {_TAGS[type(tx)]} {fields})"


# ---------------------------------------------------------------------------
# corpus helpers
# ---------------------------------------------------------------------------

def _addr(b: int) -> Bytes20:
    return Bytes20(bytes(19) + bytes([b]))


def _hash(b: int) -> Bytes32:
    return Bytes32(bytes(31) + bytes([b]))


def _legacy() -> LegacyTransaction:
    return LegacyTransaction(
        nonce=U64(1), gas_price=Uint(7), gas=Uint(21000), to=_addr(1),
        value=U256(5), data=Bytes(b""), v=U256(27), r=U256(2), s=U256(3))


def _access_list_tx() -> AccessListTransaction:
    return AccessListTransaction(
        chain_id=U64(1), nonce=U64(2), gas_price=Uint(9), gas=Uint(30000),
        to=_addr(2), value=U256(0), data=Bytes(b"\x01\x02"),
        access_list=(Access(account=_addr(3), slots=(_hash(4), _hash(5))),),
        y_parity=U256(0), r=U256(6), s=U256(7))


def _fee_market_tx() -> FeeMarketTransaction:
    return FeeMarketTransaction(
        chain_id=U64(1), nonce=U64(3), max_priority_fee_per_gas=Uint(2),
        max_fee_per_gas=Uint(11), gas=Uint(50000), to=_addr(4), value=U256(1),
        data=Bytes(b"\xaa"), access_list=(), y_parity=U256(1), r=U256(8),
        s=U256(9))


def _blob_tx() -> BlobTransaction:
    return BlobTransaction(
        chain_id=U64(1), nonce=U64(4), max_priority_fee_per_gas=Uint(3),
        max_fee_per_gas=Uint(13), gas=Uint(60000), to=_addr(5), value=U256(0),
        data=Bytes(b""), access_list=(), max_fee_per_blob_gas=U256(10),
        blob_versioned_hashes=(_hash(6), _hash(7)),
        y_parity=U256(0), r=U256(12), s=U256(13))


def _set_code_tx() -> SetCodeTransaction:
    auth = Authorization(
        chain_id=U64(1), address=_addr(8), nonce=U64(0), y_parity=U256(1),
        r=U256(14), s=U256(15))
    return SetCodeTransaction(
        chain_id=U64(1), nonce=U64(5), max_priority_fee_per_gas=Uint(4),
        max_fee_per_gas=Uint(17), gas=Uint(70000), to=_addr(6), value=U256(2),
        data=Bytes(b"\xbb"), access_list=(), authorizations=(auth,),
        y_parity=U256(0), r=U256(16), s=U256(17))


def _encode(tx) -> bytes:
    """Full envelope bytes (typed prefix + RLP, or plain legacy RLP)."""
    if isinstance(tx, LegacyTransaction):
        return bytes(rlp.encode(tx))
    return bytes(_txs.encode_transaction(tx))


# ---------------------------------------------------------------------------
# corpus
# ---------------------------------------------------------------------------

def boundary_cases() -> Iterable[bytes]:
    # Valid envelopes, one per variant.
    legacy = _legacy()
    al = _access_list_tx()
    fm = _fee_market_tx()
    blob = _blob_tx()
    sc = _set_code_tx()
    for tx in (legacy, al, fm, blob, sc):
        yield _encode(tx)

    legacy_bytes = _encode(legacy)
    fields = list(rlp.decode(legacy_bytes))

    def legacy_with(items) -> bytes:
        return bytes(rlp.encode(items))

    # GH #11986 class: leading-zero scalar v (legacy).  Must reject.
    lz = list(fields)
    lz[6] = b"\x00\x1b"  # v = 27 with a leading zero
    yield legacy_with(lz)
    # Leading-zero nonce (typed fee-market path).
    fm_fields = list(rlp.decode(_encode(fm)[1:]))
    fm_lz = list(fm_fields)
    fm_lz[1] = b"\x00\x03"
    yield b"\x02" + bytes(rlp.encode(fm_lz))
    # 9-byte legacy nonce: LEGAL — nonce is U256 (reference has no width
    # bound, model is `some 32`).  Accept on both sides.
    wide = list(fields)
    wide[0] = b"\x01" + bytes(8)
    yield legacy_with(wide)
    # 33-byte legacy nonce: U256 caps at 32 bytes; model `some 32` — reject.
    wide_n = list(fields)
    wide_n[0] = b"\x01" + bytes(32)
    yield legacy_with(wide_n)
    # Overlong U256: 33-byte legacy r.  Must reject.
    wide_r = list(fields)
    wide_r[7] = b"\x01" + bytes(32)
    yield legacy_with(wide_r)
    # Legacy field counts 8 and 10.  Must reject.
    yield legacy_with(fields[:8])
    yield legacy_with(fields + [b"\x00"])
    # Typed dispatch edges: 0x00, 0x05, 0x7f, 0xbf must reject (type error);
    # 0xff must reject (dispatch assert).
    for b0 in (0x00, 0x05, 0x7F, 0xBF, 0xFF):
        yield bytes([b0]) + bytes(rlp.encode(b""))
    # Legacy dispatch edges: 0xc0 (empty list) and 0xfe+0x00 trailing garbage.
    yield b"\xc0"
    yield b"\xfe" + b"\x00"
    # Trailing bytes after a valid legacy envelope.  Must reject.
    yield legacy_bytes + b"\x00"
    # Non-list top-level legacy RLP.  Must reject.
    yield bytes(rlp.encode(b"\x01"))
    # Access list with a 33-byte storage key.  Must reject.
    al_bad = list(rlp.decode(_encode(al)[1:]))
    bad_acc = [[al_bad[7][0][0], [b"\x01" + bytes(32)]]]
    al_bad[7] = bad_acc
    yield b"\x01" + bytes(rlp.encode(al_bad))
    # Set-code authorization with a 19-byte address.  Must reject.
    sc_fields = list(rlp.decode(_encode(sc)[1:]))
    bad_auth = list(sc_fields[9][0])
    bad_auth[1] = bytes(19)
    sc_fields[9] = [bad_auth]
    yield b"\x04" + bytes(rlp.encode(sc_fields))
    # Empty input.  Must reject (IndexError in the reference).
    yield b""


def structured_cases(count: int, seed: int) -> Iterable[bytes]:
    """Valid variant envelopes with single-byte flips / truncation / extension."""
    gen = lcg(seed)
    bases = [_encode(t) for t in (
        _legacy(), _access_list_tx(), _fee_market_tx(), _blob_tx(),
        _set_code_tx())]
    for i in range(count):
        base = bytearray(bases[next(gen) % len(bases)])
        op = i % 3
        if op == 0 and len(base) > 2:
            pos = next(gen) % len(base)
            base[pos] ^= 1 + (next(gen) % 255)
        elif op == 1:
            del base[1 + next(gen) % (len(base) - 1):]
        else:
            base.extend(bytes([next(gen) % 256]))
        yield bytes(base)


def random_cases(count: int, seed: int) -> Iterable[bytes]:
    gen = lcg(seed)
    for _ in range(count):
        n = next(gen) % 40
        yield bytes(next(gen) % 256 for _ in range(n))


def corpus() -> Iterable[bytes]:
    yield from boundary_cases()
    yield from structured_cases(400, seed=23)
    yield from random_cases(600, seed=29)


FAMILY = Family(
    name="transaction",
    corpus=corpus,
    oracle=oracle,
    reference=pins.Vendored(
        "src/ethereum/forks/amsterdam/transactions.py", _REPO_ROOT
    ),
)
