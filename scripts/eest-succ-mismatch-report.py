#!/usr/bin/env python3
"""Report EEST successful_validation mismatches with executable-spec context.

Run after scripts/codegen-eest-stateless-check.sh has produced
gen-out/eest-run/manifest.tsv and per-case *.result.tsv files.

Recommended:
  uv run --directory execution-specs --quiet python3 \
    ../scripts/eest-succ-mismatch-report.py

The context column includes `tx_gas` entries computed with executable-spec
transaction decoding:
  g  = tx gas limit
  ir = intrinsic regular gas
  is = intrinsic state gas
  wr = worst-case regular contribution, min(TX_MAX_GAS_LIMIT, g - is)
  ws = worst-case state contribution, g - ir
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def add_execution_specs_to_path(root: Path) -> None:
    src = root / "execution-specs" / "src"
    if src.is_dir():
        sys.path.insert(0, str(src))


def unpack_zisk_input(path: Path) -> bytes:
    data = path.read_bytes()
    if len(data) < 8:
        raise ValueError("input shorter than zisk length prefix")
    n = int.from_bytes(data[:8], "little")
    blob = data[8 : 8 + n]
    if len(blob) != n:
        raise ValueError(f"input truncated: want {n} bytes, have {len(blob)}")
    return blob


def decode_context(input_path: Path) -> str:
    from ethereum.forks.amsterdam.stateless_guest import (  # type: ignore
        deserialize_stateless_input,
    )
    from ethereum.forks.amsterdam.transactions import (  # type: ignore
        TX_MAX_GAS_LIMIT,
        decode_transaction,
        validate_transaction,
    )

    blob = unpack_zisk_input(input_path)
    stateless_input = deserialize_stateless_input(blob)
    payload = stateless_input.new_payload_request.execution_payload
    tx_context = decode_tx_context(
        payload.transactions,
        block_gas_limit=int(payload.gas_limit),
        tx_max_gas_limit=int(TX_MAX_GAS_LIMIT),
        decode_transaction=decode_transaction,
        validate_transaction=validate_transaction,
    )
    return "\t".join(
        [
            f"txs={len(payload.transactions)}",
            f"gas_limit={int(payload.gas_limit)}",
            f"gas_used={int(payload.gas_used)}",
            f"bal_bytes={len(payload.block_access_list)}",
            f"public_keys={len(stateless_input.public_keys)}",
            f"headers={len(stateless_input.witness.headers)}",
            f"state_nodes={len(stateless_input.witness.state)}",
            f"codes={len(stateless_input.witness.codes)}",
            tx_context,
        ]
    )


def decode_tx_context(
    transactions,
    *,
    block_gas_limit: int,
    tx_max_gas_limit: int,
    decode_transaction,
    validate_transaction,
) -> str:
    """Return compact executable-spec gas dimensions for the transaction list."""
    if not transactions:
        return "tx_gas=empty"

    dims: list[tuple[int, int, int, int, int, bool]] = []
    regular_used_worst = 0
    first_regular_over = 0
    first_state_single_over = 0

    for i, encoded in enumerate(transactions, start=1):
        tx = decode_transaction(encoded)
        intrinsic_regular, intrinsic_state = intrinsic_split_8037(
            tx, validate_transaction
        )
        gas = int(tx.gas)
        worst_regular = min(tx_max_gas_limit, max(0, gas - intrinsic_state))
        worst_state = max(0, gas - intrinsic_regular)
        is_create = len(bytes(tx.to)) == 0
        dims.append(
            (
                gas,
                intrinsic_regular,
                intrinsic_state,
                worst_regular,
                worst_state,
                is_create,
            )
        )

        if (
            first_regular_over == 0
            and worst_regular > block_gas_limit - regular_used_worst
        ):
            first_regular_over = i
        regular_used_worst += worst_regular

        if first_state_single_over == 0 and worst_state > block_gas_limit:
            first_state_single_over = i

    shown_indices = list(range(min(len(dims), 4)))
    if len(dims) > 4:
        shown_indices.append(len(dims) - 1)

    rendered = []
    for index in shown_indices:
        (
            gas,
            intrinsic_regular,
            intrinsic_state,
            worst_regular,
            worst_state,
            is_create,
        ) = dims[index]
        create_tag = ",create" if is_create else ""
        rendered.append(
            "#{}(g={},ir={},is={},wr={},ws={}{})".format(
                index + 1,
                gas,
                intrinsic_regular,
                intrinsic_state,
                worst_regular,
                worst_state,
                create_tag,
            )
        )
    if len(dims) > 5:
        rendered.insert(4, "...")

    regular_part = "regular_over=none"
    if first_regular_over:
        regular_part = f"regular_over=@{first_regular_over}"
    state_part = (
        f"single_state_over=@{first_state_single_over}"
        if first_state_single_over
        else "single_state_over=none"
    )
    return f"tx_gas={','.join(rendered)};{regular_part};{state_part}"


def intrinsic_split_8037(tx, validate_transaction) -> tuple[int, int]:
    """Return Amsterdam/EIP-8037 intrinsic regular/state gas for a decoded tx.

    The checked-in execution-specs submodule may be older than the
    tests-zkevm fixture branch and return a single intrinsic gas value. Keep the
    report useful for these fixtures by locally mirroring the EIP-8037 split.
    """
    try:
        intrinsic = validate_transaction(tx)
    except Exception:
        intrinsic = None
    if (
        intrinsic is not None
        and hasattr(intrinsic, "regular")
        and hasattr(intrinsic, "state")
    ):
        return int(intrinsic.regular), int(intrinsic.state)

    data = bytes(tx.data)
    zero_bytes = data.count(0)
    nonzero_bytes = len(data) - zero_bytes
    tokens_in_calldata = zero_bytes + 4 * nonzero_bytes

    create_regular = 0
    create_state = 0
    if len(bytes(tx.to)) == 0:
        create_state = 120 * 1530
        create_regular = 9000 + 2 * ((len(data) + 31) // 32)

    access_list_regular = 0
    access_list_floor_tokens = 0
    for access in getattr(tx, "access_list", ()):
        slot_count = len(access.slots)
        access_list_regular += 2400 + 1900 * slot_count
        access_list_floor_tokens += 80 + 128 * slot_count

    authorizations = getattr(tx, "authorizations", ())
    auth_regular = 7500 * len(authorizations)
    auth_state = (120 + 23) * 1530 * len(authorizations)

    intrinsic_regular = (
        21000
        + 4 * tokens_in_calldata
        + create_regular
        + access_list_regular
        + 16 * access_list_floor_tokens
        + auth_regular
    )
    intrinsic_state = create_state + auth_state
    return intrinsic_regular, intrinsic_state


def main() -> int:
    root = repo_root()
    add_execution_specs_to_path(root)

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=root / "gen-out" / "eest-run" / "manifest.tsv",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=None,
        help="directory containing *.result.tsv (default: manifest parent)",
    )
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()

    manifest = args.manifest
    results_dir = args.results_dir or manifest.parent
    if not manifest.is_file():
        raise SystemExit(f"manifest not found: {manifest}")

    printed = 0
    print(
        "\t".join(
            [
                "label",
                "guest_succ",
                "expected_succ",
                "context",
                "fixture",
            ]
        )
    )
    with manifest.open() as f:
        for line in f:
            fields = line.rstrip("\n").split("\t")
            if len(fields) == 6:
                label, input_file, expected_hex, _succ_bit, _input_len, relpath = fields
            elif len(fields) == 7:
                (
                    label,
                    input_file,
                    expected_hex,
                    _succ_bit,
                    _input_len,
                    _gas_limit,
                    relpath,
                ) = fields
            else:
                raise ValueError(f"unexpected manifest column count: {len(fields)}")
            input_path = Path(input_file)
            if not input_path.is_absolute() and not input_path.is_file():
                input_path = repo_root() / input_path
            result = results_dir / f"{label}.result.tsv"
            if not result.is_file():
                continue
            status, actual = result.read_text().rstrip("\n").split("\t", 1)
            if status != "OK":
                continue
            expected = expected_hex[:210]
            guest_succ = actual[64:66]
            expected_succ = expected[64:66]
            if guest_succ == expected_succ:
                continue
            try:
                context = decode_context(input_path)
            except Exception as exc:
                context = f"decode_error={type(exc).__name__}:{exc}"
            print(
                "\t".join(
                    [
                        label,
                        guest_succ,
                        expected_succ,
                        context,
                        relpath,
                    ]
                )
            )
            printed += 1
            if args.limit and printed >= args.limit:
                break
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
