#!/usr/bin/env python3
"""Compare two `codegen-eest-stateless-check` run dirs — with self-checks.

    scripts/eest-ab-compare.py BASE_RUN_DIR CANDIDATE_RUN_DIR

Reports the FA/FR delta between a base run and a candidate run, where FA/FR are
judged on the SUCC BIT (byte 32 of the guest output) against each manifest's
recorded expectation:

    guest succ=1, expected succ=0  ->  FALSE ACCEPT  (inviolable: must stay 0)
    guest succ=0, expected succ=1  ->  FALSE REJECT  (allowed; fewer is better)

WHY THIS EXISTS
---------------
Three ways an A/B number silently becomes meaningless, all hit in practice:

1. TRUNCATED ENUMERATION.  `ls DIR/*.result.tsv` exceeds ARG_MAX on a
   full-corpus run dir (72k+ files), so the counter reports 0 — which reads as a
   clean sweep rather than a broken instrument.  See #10536 / #10538.  This
   script enumerates with `os.scandir`, in-process, so there is no argv limit.

2. SHORT DENOMINATOR.  An `FA=0` computed over a subset of the manifest is not
   `FA=0`.  Asserted below: each side must have scored every manifest row (a
   candidate may be a deliberate `--limit` sample; the BASE may not).

3. LOSSY JOIN.  This is the subtle one.  Matching two runs on a label or a
   fixture path silently collapses rows via key collisions — measured on a real
   corpus: joining on the label minus its run-order prefix mapped 600 rows to
   368, and joining on fixture relpath mapped them to 166.  Either reports
   "byte-identical" over a 28-61% denominator while looking like a clean pass.

   No manifest field can join two runs: only the label is unique
   (26104/26104), and it carries a run-ORDER prefix, so a shuffled `--random`
   run does not share it.  Every content field collides — stripped label 15050,
   relpath 3149, expected-hex 21476, and pair-keys 22285/23014 out of 26104.

   So the join key here is the SHA-256 OF EACH CASE'S INPUT BYTES, which is the
   real identity of a test case.  That key is NOT injective either — measured on
   the corpus, 1232 digests cover 5845 rows, because the same guest input appears
   under several manifest labels.  That is fine, and the script asserts the
   property that actually makes it fine: WITHIN a digest group, every case on a
   side must have the SAME guest output.  It must, since the emulator is
   deterministic and the input is byte-identical — so a violation means
   non-determinism, which is itself a finding rather than a join problem.
   (Verified on the corpus: 0 of 1232 groups disagree, on guest output or on
   expected output.)  Coverage is then asserted separately: every candidate case
   must have a base counterpart.

A denominator can be destroyed by a lossy join, not only by a truncated
enumeration.  So before trusting any cross-run comparison, establish that the
join is SOUND — either injective, or many-to-one with the property that makes
collapsing harmless asserted rather than assumed.  This script does that
mechanically, so it does not depend on whoever runs it remembering to.

Exit status: 0 if every self-check passed AND no new false accepts appeared;
1 otherwise.  A failed self-check NEVER reports a verdict.
"""

from __future__ import annotations

import hashlib
import os
import sys
from collections import defaultdict


def scan_results(run_dir: str) -> dict[str, tuple[str, str]]:
    """label -> (status, output_hex).  In-process; no argv limit (see #1 above)."""
    out: dict[str, tuple[str, str]] = {}
    suffix = ".result.tsv"
    try:
        entries = list(os.scandir(run_dir))
    except OSError as exc:
        sys.exit(f"error: cannot read run dir {run_dir}: {exc}")
    for entry in entries:
        if not entry.is_file() or not entry.name.endswith(suffix):
            continue
        label = entry.name[: -len(suffix)]
        try:
            with open(entry.path) as handle:
                fields = handle.read().strip().split("\t")
        except OSError:
            continue
        out[label] = (fields[0], fields[1] if len(fields) > 1 else "")
    return out


def read_manifest(run_dir: str) -> dict[str, tuple[str, str, str]]:
    """label -> (input_path, expected_output_hex, fixture_relpath)."""
    path = os.path.join(run_dir, "manifest.tsv")
    rows: dict[str, tuple[str, str, str]] = {}
    try:
        handle = open(path)
    except OSError as exc:
        sys.exit(f"error: cannot read manifest {path}: {exc}")
    with handle:
        for line in handle:
            cols = line.rstrip("\n").split("\t")
            if len(cols) >= 7:
                rows[cols[0]] = (cols[1], cols[2], cols[6])
    return rows


def succ(hexstr: str) -> str | None:
    """The validation bit: byte 32 of the output == hex chars [64:66]."""
    return hexstr[64:66].lower() if len(hexstr) >= 66 else None


def input_digest(path: str, cache: dict[str, str | None]) -> str | None:
    if path in cache:
        return cache[path]
    try:
        with open(path, "rb") as handle:
            digest: str | None = hashlib.sha256(handle.read()).hexdigest()
    except OSError:
        digest = None
    cache[path] = digest
    return digest


def classify(results, manifest):
    """-> (false_accepts, false_rejects, agreeing, unclassified) as label lists."""
    fa, fr, agree, unknown = [], [], [], []
    for label, (_status, out_hex) in results.items():
        entry = manifest.get(label)
        if entry is None:
            unknown.append(label)
            continue
        guest, expected = succ(out_hex), succ(entry[1])
        if guest is None or expected is None:
            unknown.append(label)
            continue
        guest_ok, expected_ok = guest == "01", expected == "01"
        if guest_ok and not expected_ok:
            fa.append(label)
        elif expected_ok and not guest_ok:
            fr.append(label)
        else:
            agree.append(label)
    return fa, fr, agree, unknown


def build_join(results, manifest, cache, side: str):
    """digest -> representative label, asserting WITHIN-GROUP output consistency.

    The digest is not injective (the same guest input recurs under several
    labels), which is harmless — but only because every case sharing an input
    must produce the same guest output.  That is asserted rather than assumed: a
    violation means non-determinism, which is a finding in its own right.
    """
    by_digest: dict[str, list[str]] = defaultdict(list)
    missing = 0
    for label in results:
        entry = manifest.get(label)
        if entry is None:
            missing += 1
            continue
        digest = input_digest(entry[0], cache)
        if digest is None:
            missing += 1
            continue
        by_digest[digest].append(label)

    grouped = {d: ls for d, ls in by_digest.items() if len(ls) > 1}
    inconsistent = {d: ls for d, ls in grouped.items()
                    if len({results[l] for l in ls}) > 1}
    if grouped:
        print(f"note: {side} side has {len(grouped)} shared-input group(s) covering "
              f"{sum(len(v) for v in grouped.values())} rows (join is many-to-one)")
    if inconsistent:
        print(f"!! NON-DETERMINISM on the {side} side: {len(inconsistent)} group(s) of "
              "byte-identical inputs produced DIFFERENT guest outputs")
        for digest, labels in list(inconsistent.items())[:3]:
            print(f"     {digest[:16]}… -> {len(labels)} labels disagree, "
                  f"e.g. {labels[0][:70]}")
    if missing:
        print(f"!! {missing} row(s) on the {side} side have no readable input file")
    return {d: ls[0] for d, ls in by_digest.items()}, (not inconsistent and not missing)


def main() -> int:
    if len(sys.argv) != 3:
        sys.exit(f"usage: {os.path.basename(sys.argv[0])} BASE_RUN_DIR CANDIDATE_RUN_DIR")
    base_dir, cand_dir = sys.argv[1], sys.argv[2]

    base_res, cand_res = scan_results(base_dir), scan_results(cand_dir)
    base_man, cand_man = read_manifest(base_dir), read_manifest(cand_dir)

    print(f"base      {base_dir}: {len(base_res)} scored / {len(base_man)} manifest rows")
    print(f"candidate {cand_dir}: {len(cand_res)} scored / {len(cand_man)} manifest rows")

    ok = True

    # Self-check 2: denominators.  A candidate may be a deliberate --limit
    # sample; a BASE that did not score every row cannot anchor a delta.
    if len(base_res) != len(base_man):
        print(f"!! BASE INCOMPLETE: {len(base_res)} scored vs {len(base_man)} manifest rows "
              f"({len(base_man) - len(base_res)} missing) -- cannot anchor a delta")
        ok = False
    if len(cand_res) != len(cand_man):
        print(f"!! CANDIDATE INCOMPLETE: {len(cand_res)} scored vs {len(cand_man)} rows")
        ok = False
    sampled = len(cand_man) < len(base_man)
    if sampled:
        print(f"note: candidate is a SAMPLE ({len(cand_man)} of {len(base_man)}); "
              "reporting spot-confirmation over the sample, not a corpus delta")

    # Self-check 3: join-key uniqueness, on both sides, before any comparison.
    cache: dict[str, str | None] = {}
    base_join, base_ok = build_join(base_res, base_man, cache, "base")
    cand_join, cand_ok = build_join(cand_res, cand_man, cache, "candidate")
    ok = ok and base_ok and cand_ok

    common = set(cand_join) & set(base_join)
    coverage = len(common)
    unmatched = len(cand_join) - coverage
    print(f"joined on input-byte digest: {coverage} matched, {unmatched} unmatched")
    if unmatched:
        print(f"!! {unmatched} candidate case(s) have no base counterpart -- coverage incomplete")
        ok = False

    if not ok:
        print("\nSELF-CHECKS FAILED -- refusing to report a verdict. "
              "An FA/FR number over a broken denominator or a lossy join is not a result.")
        return 1
    print("self-checks: PASS (denominators complete, join sound "
          "— many-to-one with within-group output consistency asserted — coverage total)")

    bfa, bfr, bagree, bunk = classify(base_res, base_man)
    cfa, cfr, cagree, cunk = classify(cand_res, cand_man)
    print(f"\nbase      : FA={len(bfa)} FR={len(bfr)} agree={len(bagree)} unclassified={len(bunk)}")
    print(f"candidate : FA={len(cfa)} FR={len(cfr)} agree={len(cagree)} unclassified={len(cunk)}")

    status_diff, output_diff = [], []
    for digest in common:
        c, b = cand_res[cand_join[digest]], base_res[base_join[digest]]
        if c[0] != b[0]:
            status_diff.append(digest)
        if c[1] != b[1]:
            output_diff.append(digest)

    # FA/FR deltas are only meaningful corpus-wide; over a sample, report the
    # per-case comparison instead of a difference of two differently-sized sets.
    if not sampled:
        print(f"\nDELTA: FA {len(bfa)}->{len(cfa)} ({len(cfa) - len(bfa):+d})   "
              f"FR {len(bfr)}->{len(cfr)} ({len(cfr) - len(bfr):+d})")
        new_fa = set(cfa) - set(bfa)
        print(f"NEW FALSE ACCEPTS (must be empty): {len(new_fa)}")
        for label in sorted(new_fa)[:20]:
            print("   FA+", cand_man.get(label, ('', '', label))[2])
        if set(cfr) == set(bfr):
            print(f"FR LABEL-SET EQUALITY: PASS -- identical {len(cfr)}-label sets "
                  "(set equality, not a count match)")
        else:
            print(f"FR LABEL-SET EQUALITY: differs -- "
                  f"new={len(set(cfr) - set(bfr))} fixed={len(set(bfr) - set(cfr))}")
    else:
        new_fa = {label for label in cfa if label not in set(bfa)}

    print(f"\nstatus differences on joined cases : {len(status_diff)}")
    print(f"output-byte differences            : {len(output_diff)}")
    for digest in sorted(output_diff)[:20]:
        label = cand_join[digest]
        print("   OUT", cand_man.get(label, ('', '', label))[2])

    if not status_diff and not output_diff:
        scope = f"all {coverage} sampled cases" if sampled else f"all {coverage} cases"
        print(f"\nVERDICT: candidate is BYTE-IDENTICAL to base on {scope}.")
    return 1 if new_fa else 0


if __name__ == "__main__":
    sys.exit(main())
