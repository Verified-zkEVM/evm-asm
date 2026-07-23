#!/usr/bin/env python3
"""Single-ELF full-corpus EEST sweep — classify every fixture as FA / FR / OK / FAULT.

Runs one guest ELF (via the Spike runner) over every framed input listed in a
manifest, compares each guest verdict against the fixture's oracle expectation,
and reports the aggregate FA / FR / OK / FAULT counts (plus a per-fixture TSV).

Classification (per fixture):
  * guest verdict  = byte 32 of the guest output (the successful_validation bit).
  * oracle verdict = the manifest's succ_bit column.
  * FA    (false-accept, P0 soundness): guest succ=1 but oracle succ=0.
  * FR    (false-reject):               guest succ=0 but oracle succ=1.
  * OK:    guest and oracle agree (and, for accepted blocks, the output bytes
           match the manifest's expected prefix).
  * FAULT: emulator non-zero exit, timeout, or missing/short output.

For an A/B, run this twice (candidate ELF and a freshly-rebuilt parent ELF) over
the SAME manifest and diff the two TSVs. FA=0 is the inviolable gate; FR deltas
are the frontier signal. NOTE: byte 32 is the reliable pass/reject bit; the
guest's internal bv_fail_code is NOT in the normal output (expose it via a
debug build's OUTPUT+112 export if you need the failure *code* for a histogram).

Manifest format: tab-separated, >=7 columns; columns used are
  [0] label   [1] input-path   [2] expected-output-hex   [3] oracle succ_bit
"""
import argparse
import os
import shutil
import subprocess
import sys
import tempfile
import threading
from collections import Counter
from concurrent.futures import ThreadPoolExecutor


def default_spike():
    # Prefer an explicit env override, else the in-repo runner, else a bare name.
    env = os.environ.get("SPIKE_RUN")
    if env:
        return env
    here = os.path.dirname(os.path.abspath(__file__))
    repo_runner = os.path.join(here, "spike", "spike_run")
    return repo_runner if os.path.exists(repo_runner) else "spike_run"


def parse_args(argv=None):
    p = argparse.ArgumentParser(
        description="Single-ELF full-corpus EEST sweep (FA/FR/OK/FAULT).",
        epilog=(
            "examples:\n"
            "  # basic sweep\n"
            "  WORKERS=20 scripts/sweep_one.py gen-out/regionmap/stateless_guest.elf /tmp/cand.tsv\n"
            "  # explicit runner + manifest\n"
            "  scripts/sweep_one.py --spike scripts/spike/spike_run \\\n"
            "      --manifest /tmp/fc668/in/manifest.tsv cand.elf cand.tsv\n"
            "  # A/B: sweep candidate and a fresh parent over the same manifest, then diff the TSVs\n"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("elf", help="path to the guest ELF to sweep")
    p.add_argument("out", help="path to write the per-fixture result TSV")
    p.add_argument(
        "--manifest",
        default=os.environ.get("SWEEP_MANIFEST", "/tmp/fc668/in/manifest.tsv"),
        help="manifest TSV (label\\tinput\\texpected_hex\\tsucc_bit\\t...); "
        "default $SWEEP_MANIFEST or /tmp/fc668/in/manifest.tsv",
    )
    p.add_argument(
        "--spike",
        default=default_spike(),
        help="Spike runner executable; default $SPIKE_RUN, else scripts/spike/spike_run",
    )
    p.add_argument(
        "--workers",
        type=int,
        default=int(os.environ.get("WORKERS", "20")),
        help="parallel worker threads (default $WORKERS or 20)",
    )
    p.add_argument(
        "--timeout",
        type=int,
        default=int(os.environ.get("SWEEP_TIMEOUT", "120")),
        help="per-fixture emulator timeout in seconds (default 120)",
    )
    p.add_argument(
        "--dump-len",
        default=os.environ.get("SPIKE_OUTPUT_LEN", "256"),
        help="guest output bytes to capture (SPIKE_OUTPUT_LEN; default 256)",
    )
    p.add_argument(
        "--limit",
        type=int,
        default=0,
        help="sweep only the first N manifest rows (0 = all; for quick smoke checks)",
    )
    return p.parse_args(argv)


def load_rows(manifest, limit):
    rows = []
    with open(manifest) as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 7:
                continue
            rows.append((parts[0], parts[1], parts[2], parts[3]))  # label, input, exp_hex, succ_bit
    if limit > 0:
        rows = rows[:limit]
    return rows


def run_one(spike, elf, inp, tmpdir, timeout, dump_len):
    out = os.path.join(tmpdir, "o.bin")
    env = dict(os.environ)
    env["SPIKE_OUTPUT_LEN"] = str(dump_len)
    try:
        r = subprocess.run(
            [spike, elf, inp, out],
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=timeout,
        )
        rc = r.returncode
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", None, None)
    try:
        data = open(out, "rb").read()
    except Exception:
        return (rc, None, None)
    succ = data[32] if len(data) > 32 else None
    return (rc, data, succ)


def classify(spike, elf, timeout, dump_len, label, inp, exp_hex, oracle_succ):
    tid = threading.get_ident()
    tmpdir = tempfile.mkdtemp(prefix=f"s_{tid}_")
    try:
        nbytes = len(exp_hex) // 2
        rc, data, succ = run_one(spike, elf, inp, tmpdir, timeout, dump_len)
        match = (data is not None) and (data[:nbytes].hex() == exp_hex)
        fault = (rc not in (0,)) or (data is None) or (succ is None)
        s = str(succ) if succ is not None else "?"
        fa = (s == "1" and oracle_succ == "0")
        fr = (s == "0" and oracle_succ == "1")
        cat = "FA" if fa else ("FR" if fr else ("FAULT" if fault else "OK"))
        return (label, oracle_succ, s, match, rc, len(data) if data else 0, cat)
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def main(argv=None):
    args = parse_args(argv)

    if not os.path.exists(args.elf):
        sys.exit(f"error: ELF not found: {args.elf}")
    if not os.path.exists(args.manifest):
        sys.exit(f"error: manifest not found: {args.manifest}")
    if not (os.path.isabs(args.spike) and os.path.exists(args.spike)) and shutil.which(args.spike) is None:
        sys.exit(f"error: spike runner not found: {args.spike} (set --spike or $SPIKE_RUN)")

    rows = load_rows(args.manifest, args.limit)
    print(
        f"loaded {len(rows)} rows; elf={args.elf}; spike={args.spike}; "
        f"workers={args.workers}; timeout={args.timeout}s",
        flush=True,
    )

    done = [0]
    lock = threading.Lock()

    def worker(r):
        res = classify(args.spike, args.elf, args.timeout, args.dump_len, *r)
        with lock:
            done[0] += 1
            if done[0] % 500 == 0:
                print(f"  {done[0]}/{len(rows)}", flush=True)
        return res

    results = []
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        for res in ex.map(worker, rows):
            results.append(res)

    with open(args.out, "w") as f:
        f.write("label\toracle_succ\tguest_succ\tmatch\trc\tlen\tcat\n")
        for r in results:
            f.write("\t".join(str(x) for x in r) + "\n")

    cats = Counter(r[6] for r in results)
    print("\n=== CATEGORY COUNTS ===", flush=True)
    for c, n in cats.most_common():
        print(f"  {c}: {n}")
    fa = sum(1 for r in results if r[6] == "FA")
    fr = sum(1 for r in results if r[6] == "FR")
    ok = sum(1 for r in results if r[6] == "OK")
    print(f"\n*** FA={fa}  FR={fr}  OK(match valid)={ok} ***", flush=True)
    if fa:
        print("\n=== FA FIXTURES (P0 soundness) ===", flush=True)
        for r in [x for x in results if x[6] == "FA"][:50]:
            print(f"  {r[0]}  oracle={r[1]} guest_succ={r[2]} match={r[3]}")
    print("\nDONE", flush=True)
    # Exit non-zero if any FA (soundness gate), so callers/CI can detect it.
    return 1 if fa else 0


if __name__ == "__main__":
    sys.exit(main())
