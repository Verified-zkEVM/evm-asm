#!/usr/bin/env python3
"""Run a semantic-boundary-v2 diagnostic sweep against an immutable ELF.

The diagnostic schema uses output bytes 112..255.  It is intentionally
diagnostic-only and must not be used to establish production verdict results.
Set LHKN7_SELECTOR_MODE to record whether the input ELF uses normal or forced
routing.  Optional LHKN7_PROVENANCE is copied verbatim into the TSV header.

The resolved ELF path and its sha256 are printed at startup and written to the
TSV header as `# guest_elf` / `# guest_elf_sha256` (GH #10617), so a sweep is
self-describing about which artifact produced it.
"""

import csv
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
import threading
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

MANIFEST = "/tmp/fc668/in/manifest.tsv"
SPIKE = "/home/zksecurity/evm-asm4/scripts/spike/spike_run"
FULL_DENOMINATOR = 26104


def fail(message):
    raise SystemExit(message)


if len(sys.argv) not in (3, 4):
    fail(f"usage: {sys.argv[0]} ELF OUT.tsv [PRIOR_TSV]")

elf, out_tsv = sys.argv[1:3]
prior_tsv = sys.argv[3] if len(sys.argv) == 4 else None
labels_file = os.environ.get("LHKN7_LABELS_FILE")
workers = int(os.environ.get("WORKERS", "30"))
selector_mode = os.environ.get("LHKN7_SELECTOR_MODE")
if selector_mode not in {"forced", "normal"}:
    fail("set LHKN7_SELECTOR_MODE=forced or normal")

with open(MANIFEST) as source:
    rows = [tuple(line.rstrip("\n").split("\t")[:4]) for line in source
            if len(line.rstrip("\n").split("\t")) >= 7]
if len(rows) != FULL_DENOMINATOR:
    fail(f"manifest denominator mismatch: {len(rows)} != {FULL_DENOMINATOR}")

if prior_tsv and labels_file:
    fail("use either PRIOR_TSV or LHKN7_LABELS_FILE, not both")
mode = "full-manifest"
if labels_file:
    with open(labels_file) as source:
        wanted = {line.strip() for line in source if line.strip()}
    rows = [row for row in rows if row[0] in wanted]
    if len(rows) != len(wanted):
        fail(f"selected labels missing from manifest: wanted={len(wanted)} found={len(rows)}")
    mode = "focused-label-file"
    print(f"focused mode: {len(rows)} labels selected from {labels_file}", flush=True)
elif prior_tsv:
    with open(prior_tsv) as source:
        prior_meta = [line.rstrip("\n") for line in source if line.startswith("#")]
    prior_selector = next((line.split("=", 1)[1] for line in prior_meta
                           if line.startswith("# selector_mode=")), None)
    if prior_selector != selector_mode:
        fail(f"selector-mode mismatch: candidate={selector_mode} prior={prior_selector!r}")
    with open(prior_tsv) as source:
        prior_rows = list(csv.DictReader(
            (line for line in source if not line.startswith("#")), delimiter="\t"))
    if len(prior_rows) != FULL_DENOMINATOR:
        fail(f"prior denominator mismatch: {len(prior_rows)} != {FULL_DENOMINATOR}")
    wanted = {row["label"] for row in prior_rows if row["cat"] == "FR"}
    rows = [row for row in rows if row[0] in wanted]
    if len(rows) != len(wanted):
        fail(f"focused labels missing from manifest: wanted={len(wanted)} found={len(rows)}")
    mode = "focused-prior-FR"
    print(f"focused mode: {len(rows)} labels selected from {prior_tsv}", flush=True)

# GH #10617: state the artifact's identity before using it, and record it in the
# header.  A sweep whose ELF sha is written down cannot later be mistaken for a
# sweep of a different build -- which is how a superseded forced-routing ELF made
# a whole failure surface look phantom.
try:
    with open(elf, "rb") as handle:
        elf_sha = hashlib.sha256(handle.read()).hexdigest()
except OSError as exc:
    fail(f"cannot read ELF {elf}: {exc}")
elf_abs = os.path.abspath(elf)
print(f"loaded {len(rows)} rows; elf={elf_abs}; workers={workers}", flush=True)
print(f"  elf sha256={elf_sha}", flush=True)


def classify(row):
    label, inp, expected_hex, oracle_succ = row
    tmpdir = tempfile.mkdtemp(prefix=f"lhkn7_{threading.get_ident()}_")
    try:
        output = os.path.join(tmpdir, "out.bin")
        try:
            env = dict(os.environ, SPIKE_OUTPUT_LEN="256")
            result = subprocess.run([SPIKE, elf, inp, output], env=env,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                    timeout=120)
            rc = result.returncode
        except subprocess.TimeoutExpired:
            return (label, oracle_succ, "?", *([""] * 18), False, "TIMEOUT", 0, "FAULT")
        try:
            data = open(output, "rb").read()
        except OSError:
            data = b""
        succ = str(data[32]) if len(data) > 32 else "?"
        words = [int.from_bytes(data[offset:offset + 8], "little")
                 if len(data) >= offset + 8 else "" for offset in range(112, 256, 8)]
        match = len(data) >= len(expected_hex) // 2 and data[:len(expected_hex) // 2].hex() == expected_hex
        fault = rc != 0 or len(data) <= 32
        cat = "FA" if succ == "1" and oracle_succ == "0" else (
            "FR" if succ == "0" and oracle_succ == "1" else ("FAULT" if fault else "OK"))
        return (label, oracle_succ, succ, *words, match, rc, len(data), cat)
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


done = 0
lock = threading.Lock()


def report(row):
    global done
    value = classify(row)
    with lock:
        done += 1
        if done % 500 == 0:
            print(f"  {done}/{len(rows)}", flush=True)
    return value


with ThreadPoolExecutor(max_workers=workers) as executor:
    results = list(executor.map(report, rows))
if len(results) != len(rows):
    fail(f"result denominator mismatch: {len(results)} != {len(rows)}")

with open(out_tsv, "w") as output:
    fields = ["label", "oracle_succ", "guest_succ"] + [f"u64_{offset}" for offset in range(112, 256, 8)] + ["match", "rc", "len", "cat"]
    output.write("# schema=semantic-boundary-v2\n")
    output.write(f"# selector_mode={selector_mode}\n")
    output.write(f"# guest_elf={elf_abs}\n")
    output.write(f"# guest_elf_sha256={elf_sha}\n")
    if provenance := os.environ.get("LHKN7_PROVENANCE"):
        output.write(f"# provenance={provenance}\n")
    output.write(f"# selected_rows={len(rows)}; mode={mode}; root-analysis population=FR rows only\n")
    output.write("\t".join(fields) + "\n")
    for result in results:
        output.write("\t".join(map(str, result)) + "\n")

counts = Counter(row[-1] for row in results)
codes = Counter(row[3] for row in results if row[-1] == "FR")
print(f"DONE denominator={len(results)} categories={dict(counts)}", flush=True)
print(f"FR internal-code census={dict(codes)}", flush=True)
