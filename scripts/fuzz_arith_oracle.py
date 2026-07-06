#!/usr/bin/env python3
"""execution-specs differential oracle for the six EVM arithmetic opcodes.

Phase 3 / R-E1 (agent-progress-steering rollout). Reads operands JSONL on
stdin (one ``{"op","a","b","n"}`` object per line, hex values) and writes the
same objects to stdout with an ``"expected"`` field holding the
execution-specs *amsterdam* result.

This is the AUTHORITATIVE differential oracle for the nightly fuzz tier. It
drives the UNMODIFIED execution-specs instruction handlers (via a duck-typed
stub frame), so it is genuinely independent of evm-asm's Lean definitions.

It is a TEST ORACLE ONLY: it is never imported into Lean or the trusted base
(report 6 non-goal). Run it inside the pinned ``execution-specs`` submodule
under ``uv run`` so the spec's dependencies resolve — see
``scripts/fuzz-arith-diff.sh``.
"""

import json
import sys
from types import SimpleNamespace

from ethereum_types.numeric import U256, Uint
from ethereum.forks.amsterdam.vm.instructions import arithmetic as A

# opcode name -> (handler, arity)
OPS = {
    "div": (A.div, 2),
    "mod": (A.mod, 2),
    "sdiv": (A.sdiv, 2),
    "smod": (A.smod, 2),
    "mulmod": (A.mulmod, 3),
    "addmod": (A.addmod, 3),
}


def evm_op(op: str, a: int, b: int, n: int) -> int:
    """Run one opcode handler and return the integer result it pushes.

    EVM ``pop`` takes the top (last) element. The binary ops read dividend
    first then divisor, so the stack is ``[divisor, dividend]``. The ternary
    ops read x, y, z, so the stack is ``[z, y, x]``.
    """
    fn, arity = OPS[op]
    if arity == 2:
        stack = [U256(b), U256(a)]
    else:
        stack = [U256(n), U256(b), U256(a)]
    # Duck-typed frame: the handlers only touch .stack, .gas_left, .pc.
    evm = SimpleNamespace(stack=stack, gas_left=Uint(10**9), pc=Uint(0))
    fn(evm)
    return int(evm.stack[-1])


def main() -> int:
    out = sys.stdout
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        o = json.loads(line)
        a = int(o["a"], 16)
        b = int(o["b"], 16)
        n = int(o.get("n", "0x0"), 16)
        res = evm_op(o["op"], a, b, n)
        o["expected"] = "0x" + format(res, "x")
        out.write(json.dumps(o, separators=(",", ":")) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
