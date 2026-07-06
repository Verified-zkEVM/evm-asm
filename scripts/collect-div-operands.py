#!/usr/bin/env python3
"""Collect real mainnet DIV/MOD/SDIV/SMOD operands via opcode-level tracing.

Phase 2 of the DIV-perf effort (see docs/divmod-evm-workload.md). This is the
*gold tier* data source: it replays real mainnet transactions through an
archive node's `debug_traceTransaction` with a custom JS tracer that emits the
top-two stack items at every DIV(0x04)/MOD(0x06)/SDIV(0x05)/SMOD(0x07) opcode.
Because we trace whole blocks tx-by-tx, the resulting operand stream is
*frequency-representative*: a contract that executes many divisions contributes
proportionally many samples, so DeFi math dominates naturally.

Default endpoint is drpc.org's free tier, which (as of 2026-06) serves
`debug_traceTransaction` with custom tracers without an API key. Full-block
opcode tracing times out on the free tier, so we trace one transaction per
request (each ~0.1-0.3s) and parallelise with a small thread pool.

Output: newline-delimited JSON, one record per division op:
    {"blk": <int>, "tx": "0x..", "op": 4|5|6|7, "a": "<hex dividend>", "b": "<hex divisor>"}

Usage:
    # 40 blocks strided back from chain head:
    python3 scripts/collect-div-operands.py --count 40 --stride 9973 -o bench/div-operands-mainnet.jsonl
    # explicit block list:
    python3 scripts/collect-div-operands.py --blocks 25427968,25400000 -o out.jsonl
    # different endpoint:
    python3 scripts/collect-div-operands.py --rpc https://your-node --count 10
"""
import argparse
import json
import sys
import time
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed

DEFAULT_RPC = "https://eth.drpc.org"

# JS tracer: emit "op|dividend_hex|divisor_hex" for each DIV/MOD/SDIV/SMOD.
# peek(0) is stack top = first operand popped (the dividend / numerator);
# peek(1) is the divisor / denominator, matching the EVM spec's pop order.
TRACER = """{
  d: [],
  step: function(log, db) {
    var op = log.op.toNumber();
    if (op==4||op==5||op==6||op==7) {
      this.d.push(op + "|" + log.stack.peek(0).toString(16) + "|" + log.stack.peek(1).toString(16));
    }
  },
  fault: function(log, db) {},
  result: function(ctx, db) { return this.d; }
}"""


def rpc(url, method, params, timeout=45, retries=2):
    body = json.dumps({"jsonrpc": "2.0", "method": method, "params": params, "id": 1}).encode()
    last = None
    for attempt in range(retries):
        try:
            req = urllib.request.Request(
                url, data=body,
                headers={"content-type": "application/json", "user-agent": "curl/8.5.0"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                out = json.loads(r.read())
            if "error" in out:
                # Server-side trace timeout (408) on a heavy tx won't get better
                # on retry; give up immediately so we don't grind for minutes.
                raise RuntimeError(out["error"])
            return out["result"]
        except Exception as e:  # noqa: BLE001
            last = e
            time.sleep(0.3 * (attempt + 1))
    raise last


def head_block(url):
    return int(rpc(url, "eth_blockNumber", []), 16)


def block_txs(url, blk):
    b = rpc(url, "eth_getBlockByNumber", [hex(blk), False])
    if b is None:
        return []
    return b.get("transactions") or b.get("txs") or []


def trace_tx(url, tx):
    res = rpc(url, "debug_traceTransaction", [tx, {"tracer": TRACER}])
    out = []
    for entry in res or []:
        op_s, a, b = entry.split("|", 2)
        out.append((int(op_s), a, b))
    return out


def collect_block(url, blk, workers, fail_breaker=60):
    txs = block_txs(url, blk)
    records = []
    fails = ok = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futs = {ex.submit(trace_tx, url, tx): tx for tx in txs}
        for fut in as_completed(futs):
            tx = futs[fut]
            try:
                for op, a, b in fut.result():
                    records.append({"blk": blk, "tx": tx, "op": op, "a": a, "b": b})
                ok += 1
            except Exception as e:  # noqa: BLE001
                fails += 1
                print(f"  ! tx {tx[:12]} failed: {e}", file=sys.stderr)
                # circuit breaker: endpoint is throttling/down for this block —
                # stop grinding and move on rather than retrying every tx.
                if fails >= fail_breaker and ok == 0:
                    print(f"  !! block {blk}: {fails} failures, 0 ok -> skipping rest",
                          file=sys.stderr)
                    for f in futs:
                        f.cancel()
                    break
    return len(txs), records, fails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rpc", default=DEFAULT_RPC)
    ap.add_argument("--blocks", help="comma-separated explicit block numbers")
    ap.add_argument("--count", type=int, default=40, help="number of blocks to sample")
    ap.add_argument("--stride", type=int, default=9973, help="gap between sampled blocks (prime to avoid alignment)")
    ap.add_argument("--head", type=int, help="start block (default: chain head)")
    ap.add_argument("--workers", type=int, default=8, help="concurrent traces per block")
    ap.add_argument("-o", "--out", required=True)
    args = ap.parse_args()

    if args.blocks:
        blocks = [int(x) for x in args.blocks.split(",")]
    else:
        top = args.head if args.head is not None else head_block(args.rpc)
        blocks = [top - i * args.stride for i in range(args.count)]
    print(f"sampling {len(blocks)} blocks via {args.rpc}: {blocks[0]} .. {blocks[-1]}", file=sys.stderr)

    total_ops = 0
    with open(args.out, "w") as f:
        for i, blk in enumerate(blocks):
            t0 = time.time()
            try:
                ntx, recs, fails = collect_block(args.rpc, blk, args.workers)
            except Exception as e:  # noqa: BLE001
                print(f"[{i+1}/{len(blocks)}] block {blk} FAILED: {e}", file=sys.stderr)
                continue
            for r in recs:
                f.write(json.dumps(r) + "\n")
            f.flush()
            total_ops += len(recs)
            print(f"[{i+1}/{len(blocks)}] block {blk}: {ntx} tx ({fails} failed), "
                  f"{len(recs)} div-ops ({time.time()-t0:.1f}s, total {total_ops})",
                  file=sys.stderr)
    print(f"done: {total_ops} div-ops -> {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
