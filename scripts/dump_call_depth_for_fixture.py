#!/usr/bin/env python3
"""Dump per-tx gas + max EVM call depth (spec ground truth) for a zisk .input.

Useful for diagnosing deeply-recursive CALL-family false-rejects (e.g. the
EIP-7251 consolidation `call_depth_high` over-count, bead evm-asm-fhsxz.17):
the spec's max recursion depth and per-tx gas are the reference the guest's
block-gas-used reconstruction must match.

Run:  uv run --directory execution-specs --quiet python3 \
        ../scripts/dump_call_depth_for_fixture.py <path-to.input>
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

    import ethereum.forks.amsterdam.vm.interpreter as interp
    import ethereum.forks.amsterdam.fork as fork

    stats = {"maxdepth": 0, "calls": 0}
    orig_pm = interp.process_message

    def traced_process_message(message):  # noqa: ANN001
        d = int(message.depth)
        if d > stats["maxdepth"]:
            stats["maxdepth"] = d
        stats["calls"] += 1
        return orig_pm(message)

    interp.process_message = traced_process_message

    orig_make = fork.make_receipt
    rcpt = {"i": 0, "prev": 0}

    def traced_make_receipt(tx, error, cumulative_gas_used, logs):  # noqa: ANN001
        cg = int(cumulative_gas_used)
        print(
            f"RECEIPT[{rcpt['i']}] cumulative_gas_used={cg} "
            f"tx_gas_used={cg - rcpt['prev']} error={error is not None} "
            f"n_logs={len(logs)}"
        )
        rcpt["prev"] = cg
        rcpt["i"] += 1
        return orig_make(tx, error, cumulative_gas_used, logs)

    fork.make_receipt = traced_make_receipt

    from ethereum.forks.amsterdam.stateless_guest import run_stateless_guest

    try:
        out = run_stateless_guest(blob)
        print("run_stateless_guest OK, output_len=", len(out))
        print("succ_byte(=output[32])=", out[32] if len(out) > 32 else "n/a")
    except Exception as e:  # noqa: BLE001
        print("run_stateless_guest raised:", type(e).__name__, str(e)[:200])

    print(
        f"MAX_CALL_DEPTH_REACHED={stats['maxdepth']} "
        f"TOTAL_process_message_calls={stats['calls']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
