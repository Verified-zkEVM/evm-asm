#!/usr/bin/env python3
"""Generate a `ziskemu -i` input file containing a length-prefixed,
SSZ-encoded `SszStatelessInput` with a caller-specified `chain_id`.

Invocation (from the repo root):

    uv run --directory execution-specs --quiet python3 \
        ../scripts/stateless-gen-input.py CHAIN_ID OUT_FILE

CHAIN_ID is parsed as a Python integer literal (`int(..., 0)`), so
`1`, `0x1234567890ABCDEF`, and `1311768467294899695` are all valid.

The generated file is laid out as ziskemu expects:

    bytes [0..8)    : u64 LE length of the SSZ blob
    bytes [8..)     : SSZ-encoded SszStatelessInput

ziskemu places this verbatim at INPUT_ADDR + 8.. on guest start, after
its own 8 metadata bytes (zeroed). See `EvmAsm/Codegen/Programs.lean`
for the host-IO layout and `EvmAsm/Stateless/SSZ/Decode/Program.lean`
for the guest's reader.
"""
from __future__ import annotations

import argparse
import struct
import sys
from pathlib import Path

from stateless_input_transport import pack_stateless_input, transport_padding_length


def _rlp_encoded_test_header() -> bytes:
    """Construct + RLP-encode an amsterdam Block Header with fixed
    test field values. Used by `--with-one-real-header` so the
    fixture's `witness.headers[0]` is a real (~660-byte) header."""
    from ethereum.crypto.hash import Hash32
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes8, Bytes32
    from ethereum_types.numeric import U64, U256, Uint

    from ethereum.forks.amsterdam.blocks import Header
    from ethereum.forks.amsterdam.fork_types import Bloom

    h = Header(
        parent_hash=Hash32(b"\x11" * 32),
        ommers_hash=Hash32(b"\x22" * 32),
        coinbase=Bytes(b"\x33" * 20),
        state_root=Hash32(b"\x44" * 32),
        transactions_root=Hash32(b"\x55" * 32),
        receipt_root=Hash32(b"\x66" * 32),
        bloom=Bloom(b"\x00" * 256),
        difficulty=Uint(0),
        number=Uint(0x1234),
        gas_limit=Uint(0x1c9c380),
        gas_used=Uint(0x100),
        timestamp=U256(0x6566778899),
        extra_data=Bytes(b"evm-asm2 PR-K7"),
        prev_randao=Bytes32(b"\x77" * 32),
        nonce=Bytes8(b"\x00" * 8),
        base_fee_per_gas=Uint(0x07),
        withdrawals_root=Hash32(b"\x88" * 32),
        blob_gas_used=U64(0),
        excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(b"\x99" * 32),
        requests_hash=Hash32(b"\xaa" * 32),
        block_access_list_hash=Hash32(b"\xbb" * 32),
    )
    return rlp.encode(h)


def build_ssz_blob(
    chain_id: int,
    with_empty_header: bool,
    with_empty_state_node: bool,
    with_two_empty_headers: bool,
    with_one_real_header: bool,
) -> bytes:
    """SSZ-encode an `SszStatelessInput`.

    `chain_config.chain_id` is set from `chain_id`. Other fields are
    empty defaults, with optional witness mutations:

    - `with_empty_header=True` puts one zero-length entry in
      `witness.headers`. The witness body grows from 12 bytes
      (offsets only) to 16 bytes (offsets + a 4-byte inner offsets
      entry for the empty header).
    - `with_two_empty_headers=True` puts two zero-length entries in
      `witness.headers`. Witness body grows to 20 bytes
      (12 offsets + 8 inner offsets); the first inner u32 = 8, so
      the guest's PR6 `decode_header_count` yields 2.
    - `with_empty_state_node=True` puts one zero-length entry in
      `witness.state`. The witness body grows the same way as
      `with_empty_header`, but the mutation lives in `state` --
      `witness.headers` stays empty.

    The combinations let the test harness distinguish:
      (A) empty witness                 -> headers empty,  count=0
      (B) one empty header              -> headers !empty, count=1
      (C) two empty headers             -> headers !empty, count=2
      (D) one empty state node          -> headers empty,  count=0
                                           (state non-empty, but the
                                            guest's PR5 bool only
                                            tracks headers and PR6
                                            count only tracks headers)
    """
    from ethereum.forks.amsterdam.stateless_ssz import (
        MAX_BYTES_PER_HEADER,
        MAX_BYTES_PER_WITNESS_NODE,
        MAX_WITNESS_HEADERS,
        MAX_WITNESS_NODES,
        SszChainConfig,
        SszExecutionWitness,
        SszNewPayloadRequest,
        SszStatelessInput,
    )
    from remerkleable.byte_arrays import ByteList
    from remerkleable.complex import List as SszList

    witness_kwargs = {}
    if with_empty_header:
        witness_kwargs["headers"] = SszList[
            ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS
        ](ByteList[MAX_BYTES_PER_HEADER]())
    if with_two_empty_headers:
        witness_kwargs["headers"] = SszList[
            ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS
        ](
            ByteList[MAX_BYTES_PER_HEADER](),
            ByteList[MAX_BYTES_PER_HEADER](),
        )
    if with_one_real_header:
        header_bytes = _rlp_encoded_test_header()
        witness_kwargs["headers"] = SszList[
            ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS
        ](ByteList[MAX_BYTES_PER_HEADER](header_bytes))
    if with_empty_state_node:
        witness_kwargs["state"] = SszList[
            ByteList[MAX_BYTES_PER_WITNESS_NODE], MAX_WITNESS_NODES
        ](ByteList[MAX_BYTES_PER_WITNESS_NODE]())
    witness = SszExecutionWitness(**witness_kwargs)

    ssz_input = SszStatelessInput(
        new_payload_request=SszNewPayloadRequest(),
        witness=witness,
        chain_config=SszChainConfig(chain_id=chain_id),
        public_keys=(),
    )
    return ssz_input.encode_bytes()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "chain_id",
        help="Python integer literal (e.g. 1, 0x1234567890ABCDEF).",
    )
    parser.add_argument("out_file", type=Path)
    parser.add_argument(
        "--with-empty-header",
        action="store_true",
        help=(
            "Inject one zero-length entry into `witness.headers` so "
            "the guest's PR5 decode_validation_bit yields 0 "
            "(headers list non-empty)."
        ),
    )
    parser.add_argument(
        "--with-empty-state-node",
        action="store_true",
        help=(
            "Inject one zero-length entry into `witness.state`. PR5's "
            "bool tracks headers only, so this fixture stays at 1 "
            "(differentiates PR5 logic from PR4 logic)."
        ),
    )
    parser.add_argument(
        "--with-two-empty-headers",
        action="store_true",
        help=(
            "Inject two zero-length entries into `witness.headers`. "
            "PR6's decode_header_count should yield 2."
        ),
    )
    parser.add_argument(
        "--with-one-real-header",
        action="store_true",
        help=(
            "Inject a single RLP-encoded amsterdam Header into "
            "`witness.headers[0]`. Used by PR-K7 to test per-element "
            "extraction: the guest hashes element 0 (the header "
            "bytes), not the whole section."
        ),
    )
    parser.add_argument(
        "--hash-out",
        type=Path,
        default=None,
        help=(
            "Optionally write the SSZ `hash_tree_root` of "
            "`witness.headers[0]` (as a `ByteList[1024]`) as a "
            "64-hex-char string. PR-S10's stateless_guest stamps "
            "this into the output's `new_payload_request_root` "
            "field (replacing PR-K7's keccak stub). When "
            "`witness.headers` is empty, hashes an empty "
            "`ByteList[1024]()`."
        ),
    )
    args = parser.parse_args()

    chain_id = int(args.chain_id, 0)
    blob = build_ssz_blob(
        chain_id,
        args.with_empty_header,
        args.with_empty_state_node,
        args.with_two_empty_headers,
        args.with_one_real_header,
    )

    # The prefix continues to name exactly the SSZ blob.  Shared transport
    # framing adds ordinary dword alignment plus one mapped zero guard dword.
    # The guard makes a read defined, not correct.
    pad = transport_padding_length(len(blob))
    packed = pack_stateless_input(blob)

    args.out_file.parent.mkdir(parents=True, exist_ok=True)
    with args.out_file.open("wb") as fh:
        fh.write(packed)

    print(
        f"wrote {args.out_file}: 8 B length prefix + {len(blob)} B SSZ blob "
        f"+ {pad} B transport padding/guard = {len(packed)} B total",
        file=sys.stderr,
    )

    if args.hash_out is not None:
        # PR-S12: the guest computes SSZ `hash_tree_root` of the
        # entire `witness: ExecutionWitness` Container (3 sub-
        # lists: state, codes, headers). We extract each sub-
        # list's elements from the SSZ blob and rebuild the
        # Container via remerkleable's `SszExecutionWitness`,
        # then hash_tree_root() against that.
        import struct as _struct
        from ethereum.forks.amsterdam.stateless_ssz import (
            MAX_BYTES_PER_CODE,
            MAX_BYTES_PER_HEADER,
            MAX_BYTES_PER_WITNESS_NODE,
            MAX_WITNESS_CODES,
            MAX_WITNESS_HEADERS,
            MAX_WITNESS_NODES,
            SszExecutionWitness,
        )
        from remerkleable.byte_arrays import ByteList
        from remerkleable.complex import List as SszList

        offset_1 = _struct.unpack_from("<I", blob, 4)[0]
        offset_3 = _struct.unpack_from("<I", blob, 16)[0]
        witness_start = offset_1
        witness_end = offset_3
        witness_section = blob[witness_start:witness_end]

        # Parse 3 u32 offsets in the witness Container header.
        off_state   = _struct.unpack_from("<I", witness_section, 0)[0]
        off_codes   = _struct.unpack_from("<I", witness_section, 4)[0]
        off_headers = _struct.unpack_from("<I", witness_section, 8)[0]
        end = len(witness_section)

        def parse_list(section: bytes) -> list:
            if not section:
                return []
            first_inner = _struct.unpack_from("<I", section, 0)[0]
            n = first_inner // 4
            out = []
            for i in range(n):
                inner_i = _struct.unpack_from(
                    "<I", section, 4 * i)[0]
                el_start = inner_i
                if i + 1 < n:
                    inner_next = _struct.unpack_from(
                        "<I", section, 4 * (i + 1))[0]
                    el_end = inner_next
                else:
                    el_end = len(section)
                out.append(section[el_start:el_end])
            return out

        state_elems = parse_list(witness_section[off_state:off_codes])
        codes_elems = parse_list(witness_section[off_codes:off_headers])
        headers_elems = parse_list(witness_section[off_headers:end])

        SBL = ByteList[MAX_BYTES_PER_WITNESS_NODE]
        CBL = ByteList[MAX_BYTES_PER_CODE]
        HBL = ByteList[MAX_BYTES_PER_HEADER]
        SL = SszList[SBL, MAX_WITNESS_NODES]
        CL = SszList[CBL, MAX_WITNESS_CODES]
        HL = SszList[HBL, MAX_WITNESS_HEADERS]
        ssz_witness = SszExecutionWitness(
            state=SL(*(SBL(e) for e in state_elems)),
            codes=CL(*(CBL(e) for e in codes_elems)),
            headers=HL(*(HBL(e) for e in headers_elems)),
        )
        root = ssz_witness.hash_tree_root()
        digest = root.hex() if isinstance(root, bytes) else bytes(root).hex()
        args.hash_out.parent.mkdir(parents=True, exist_ok=True)
        with args.hash_out.open("w") as fh:
            fh.write(digest)
        print(
            f"wrote {args.hash_out}: "
            f"ssz_hash_tree_root(ExecutionWitness, state={len(state_elems)}, "
            f"codes={len(codes_elems)}, headers={len(headers_elems)}) "
            f"= {digest}",
            file=sys.stderr,
        )

    return 0


if __name__ == "__main__":
    sys.exit(main())
