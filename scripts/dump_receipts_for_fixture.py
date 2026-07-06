#!/usr/bin/env python3
"""Dump per-receipt cumulative_gas_used (spec ground truth) for a zisk .input.

Run:  uv run --directory execution-specs --quiet python3 \
        ../scripts/dump_receipts_for_fixture.py <path-to.input>
"""
from __future__ import annotations
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def add_specs(root: Path) -> None:
    src = root / "execution-specs" / "src"
    if src.is_dir():
        sys.path.insert(0, str(src))


def unpack_zisk_input(path: Path) -> bytes:
    data = path.read_bytes()
    n = int.from_bytes(data[:8], "little")
    return data[8 : 8 + n]


def main() -> int:
    root = repo_root()
    add_specs(root)
    inp = Path(sys.argv[1])
    blob = unpack_zisk_input(inp)

    import ethereum.forks.amsterdam.fork as fork

    orig_make = fork.make_receipt
    idx = {"i": 0}

    def traced_make_receipt(tx, error, cumulative_gas_used, logs):
        print(
            f"RECEIPT[{idx['i']}] cumulative_gas_used={int(cumulative_gas_used)} "
            f"error={error is not None} n_logs={len(logs)}"
        )
        idx["i"] += 1
        return orig_make(tx, error, cumulative_gas_used, logs)

    fork.make_receipt = traced_make_receipt

    from ethereum.forks.amsterdam.stateless_guest import run_stateless_guest

    try:
        out = run_stateless_guest(blob)
        print("run_stateless_guest OK, output_len=", len(out))
        print("succ_byte(=output[32])=", out[32] if len(out) > 32 else "n/a")
    except Exception as e:  # noqa: BLE001
        print("run_stateless_guest raised:", type(e).__name__, str(e)[:200])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# (appended) richer dump available by importing make_receipt trace above.
