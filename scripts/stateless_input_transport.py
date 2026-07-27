"""Shared framing for stateless-guest inputs transported to ziskemu.

The declared payload remains exactly the schema-prefixed SSZ bytes consumed by
execution-specs.  The trailing zero guard is transport-only: it gives a
dword-granular guest read immediately past the declared payload deterministic
mapped zero bytes.  It does not make an unintended guest read semantically
correct.
"""
from __future__ import annotations

import struct


LENGTH_PREFIX_BYTES = 8
GUARD_DWORD_BYTES = 8


def transport_padding_length(payload_len: int) -> int:
    """Return ordinary 8-byte alignment padding plus one zero guard dword."""
    if payload_len < 0:
        raise ValueError(f"negative payload length: {payload_len}")
    ordinary_pad = (-(LENGTH_PREFIX_BYTES + payload_len)) % GUARD_DWORD_BYTES
    return ordinary_pad + GUARD_DWORD_BYTES


def pack_stateless_input(payload: bytes) -> bytes:
    """Frame a payload without altering the bytes named by its length prefix."""
    padding = transport_padding_length(len(payload))
    return struct.pack("<Q", len(payload)) + payload + (b"\x00" * padding)


def unpack_stateless_input(packed: bytes) -> bytes:
    """Return the declared payload after validating canonical transport framing."""
    if len(packed) < LENGTH_PREFIX_BYTES:
        raise ValueError(f"packed input too short: {len(packed)}")
    payload_len = struct.unpack("<Q", packed[:LENGTH_PREFIX_BYTES])[0]
    end = LENGTH_PREFIX_BYTES + payload_len
    if len(packed) < end:
        raise ValueError(
            f"packed input truncated: length={payload_len}, bytes={len(packed)}"
        )
    padding = packed[end:]
    expected_padding = transport_padding_length(payload_len)
    if len(padding) != expected_padding:
        raise ValueError(
            "packed input has wrong padding length: "
            f"{len(padding)} (expected {expected_padding})"
        )
    if any(padding):
        raise ValueError("packed input has non-zero transport padding")
    return packed[LENGTH_PREFIX_BYTES:end]
