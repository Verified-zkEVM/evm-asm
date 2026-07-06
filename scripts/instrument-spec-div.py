#!/usr/bin/env python3
"""Instrument the execution-specs Python EVM's DIV/SDIV/MOD/SMOD ops.

This is the offline, node-free instrumentation path described in the Phase 2
plan (docs/divmod-evm-workload.md). It monkeypatches the *real* spec opcode
implementations
    ethereum.forks.<fork>.vm.instructions.arithmetic.{div,sdiv,mod,smod}
so that every invocation appends its (dividend, divisor) operands to a log, then
drives them by executing actual EVM bytecode (`PUSH32 b; PUSH32 a; OP; STOP`)
through a minimal-but-genuine interpreter loop. The division *semantics* and the
operand capture go through the unmodified spec functions; only the surrounding
state/message plumbing (irrelevant to arithmetic) is stubbed.

By default it replays the divisor-family operands from the repricing benchmark
(`execution-specs/tests/benchmark/compute/instruction/test_arithmetic.py`) — the
*adversarial* tier (worst-case divisors just over 2^64 / 2^128), NOT a frequency
distribution. The frequency-representative data comes from real mainnet traces;
see scripts/collect-div-operands.py. Output schema matches that collector so the
same analyzer (scripts/analyze-div-operands.py) consumes both.

Usage:
    execution-specs/.venv/bin/python scripts/instrument-spec-div.py \
        --fork prague -o bench/div-operands-benchmark.jsonl
    # custom pairs (hex), op in {DIV,SDIV,MOD,SMOD}:
    ... --pair DIV:0xffff..:0x100..0033
"""
import argparse
import importlib
import json
import sys
from types import SimpleNamespace

# ---- adversarial benchmark operands (verbatim from test_arithmetic.py) -------
M = (1 << 256) - 1
DEFAULT_BINOP = (
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001,
)
BENCHMARK_PAIRS = [
    # (op, dividend, divisor)
    ("DIV", 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
            0x100000000000000000000000000000033),   # divisor ~just over 2**128
    ("DIV", 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
            0x10000000000000033),                    # divisor ~just over 2**64
    ("SDIV", 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
             0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFCD),
    ("SDIV", 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
             0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFCD),
    ("MOD", DEFAULT_BINOP[0], DEFAULT_BINOP[1]),
    ("SMOD", DEFAULT_BINOP[0], DEFAULT_BINOP[1]),
]
OP_HEX = {"DIV": 0x04, "SDIV": 0x05, "MOD": 0x06, "SMOD": 0x07}

LOG = []  # list of (op_byte, dividend_int, divisor_int)


def install_hooks(fork):
    """Wrap the spec's div/sdiv/mod/smod to record operands (stack top-2)."""
    arith = importlib.import_module(f"ethereum.forks.{fork}.vm.instructions.arithmetic")
    instrs = importlib.import_module(f"ethereum.forks.{fork}.vm.instructions")
    Ops = instrs.Ops

    def make(orig, op_byte):
        def wrapped(evm):
            # spec pops top first (dividend) then next (divisor)
            a = int(evm.stack[-1]) if len(evm.stack) >= 1 else 0
            b = int(evm.stack[-2]) if len(evm.stack) >= 2 else 0
            LOG.append((op_byte, a, b))
            return orig(evm)
        return wrapped

    for name, op_byte, op_enum in (("div", 4, Ops.DIV), ("sdiv", 5, Ops.SDIV),
                                   ("mod", 6, Ops.MOD), ("smod", 7, Ops.SMOD)):
        orig = getattr(arith, name)
        wrapped = make(orig, op_byte)
        setattr(arith, name, wrapped)          # module attribute (for direct callers)
        instrs.op_implementation[op_enum] = wrapped  # dispatch table (for the loop)
    return arith


def run_bytecode(fork, code: bytes):
    """Execute `code` through the real spec opcode loop with stubbed plumbing.

    Only stack/arithmetic/push opcodes are needed here; the arithmetic ops never
    touch state, and charge_gas's only side-channel (evm_trace) is a no-op by
    default, so a stub message is sufficient and the division goes through the
    genuine spec implementation.
    """
    vm = importlib.import_module(f"ethereum.forks.{fork}.vm")
    instrs = importlib.import_module(f"ethereum.forks.{fork}.vm.instructions")
    interp = importlib.import_module(f"ethereum.forks.{fork}.vm.interpreter")
    from ethereum_types.numeric import Uint

    Ops = instrs.Ops
    op_impl = instrs.op_implementation
    valid_jumpdests = interp.get_valid_jump_destinations(code)

    evm = vm.Evm(
        pc=Uint(0), stack=[], memory=bytearray(), code=code,
        gas_left=Uint(1 << 62), valid_jump_destinations=valid_jumpdests,
        logs=(), refund_counter=0, running=True,
        message=SimpleNamespace(code_address=None), output=b"",
        accounts_to_delete=set(), return_data=b"", error=None,
        accessed_addresses=set(), accessed_storage_keys=set(),
    )
    while evm.running and evm.pc < Uint(len(evm.code)):
        op = Ops(evm.code[evm.pc])
        op_impl[op](evm)
    return evm


def push32(v):
    return bytes([0x7F]) + (v & M).to_bytes(32, "big")


def make_program(op_name, dividend, divisor):
    # stack after pushes: [divisor, dividend] (dividend on top); OP pops top=dividend
    return push32(divisor) + push32(dividend) + bytes([OP_HEX[op_name]]) + bytes([0x00])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fork", default="prague")
    ap.add_argument("--pair", action="append", default=[],
                    help="extra OP:dividend_hex:divisor_hex (repeatable)")
    ap.add_argument("-o", "--out", required=True)
    args = ap.parse_args()

    install_hooks(args.fork)

    pairs = list(BENCHMARK_PAIRS)
    for p in args.pair:
        op, a, b = p.split(":")
        pairs.append((op, int(a, 16), int(b, 16)))

    for op, a, b in pairs:
        run_bytecode(args.fork, make_program(op, a, b))

    with open(args.out, "w") as f:
        for op_byte, a, b in LOG:
            f.write(json.dumps({"blk": -1, "tx": "benchmark", "op": op_byte,
                                "a": format(a & M, "x"), "b": format(b & M, "x")}) + "\n")
    print(f"wrote {len(LOG)} div-ops (fork={args.fork}) -> {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
