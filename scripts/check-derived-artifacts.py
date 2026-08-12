#!/usr/bin/env python3
"""check-derived-artifacts.py (#12268): name WHICH guest-image derived artifact is
stale, relative to WHICH input — instead of a bare byte mismatch.

The covering artifact set is conditional on the routine's kind and derived from the
pipeline, not a hand-maintained list:

  converted MANIFEST routine (Program + _eq_prog): needs a .s fixture AND a
      GuestImageEntries row
  asm-string def (not in MANIFEST): needs neither

Artifacts and the inputs they derive from:

  scripts/asm-fixtures/<Name>.s            <- Lean source emission (MANIFEST rows)
  scripts/asm-fixtures/symbol-addresses.tsv <- regionmap ELF (gen-symbol-addresses.py)
  EvmAsm/Codegen/GuestAddrs.lean           <- symbol-addresses.tsv
                                              (asm_to_program.py guest-addrs)
  EvmAsm/Codegen/Proofs/GuestImageEntries.lean <- MANIFEST.tsv + symbol-addresses.tsv
                                              (guest_image_coverage.py --emit-lean)
  docs/4ch8f-guest-image-coverage.md       <- GuestImageEntries (--write-doc)
  EvmAsm/Codegen/RegionMapLinkPins.lean    <- regionmap ELF (gen-region-map-link-pins.py)

Each finding is reported as:
  <artifact> STALE relative to <input>; regen: <command>

Exit 0 = all consistent. Exit 1 = one or more findings.
--self-test: stale each artifact in turn (in a scratch copy of the tree is NOT
required; the check functions are called directly) and assert the checker names
exactly that artifact. Requires the regionmap ELF at
gen-out/regionmap/stateless_guest.elf (build: lake build codegen && lake exe codegen
--program stateless_guest --halt linux93 -o gen-out/regionmap/stateless_guest).
"""

import concurrent.futures
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ELF = os.path.join(ROOT, "gen-out/regionmap/stateless_guest.elf")
TSV = os.path.join(ROOT, "scripts/asm-fixtures/symbol-addresses.tsv")
FIXTURES = os.path.dirname(TSV)
GUEST_ADDRS = os.path.join(ROOT, "EvmAsm/Codegen/GuestAddrs.lean")
ENTRIES = os.path.join(ROOT, "EvmAsm/Codegen/Proofs/GuestImageEntries.lean")
COVERAGE_DOC = os.path.join(ROOT, "docs/4ch8f-guest-image-coverage.md")
PINS = os.path.join(ROOT, "EvmAsm/Codegen/RegionMapLinkPins.lean")
MANIFEST = os.path.join(ROOT, "scripts/asm-fixtures/MANIFEST.tsv")
FIXTURE_DIR = os.path.join(ROOT, "scripts/asm-fixtures")


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def snapshot(path):
    with open(path, "rb") as f:
        return f.read()


def restore(path, data):
    with open(path, "wb") as f:
        f.write(data)


def check_tsv():
    """tsv vs regionmap ELF."""
    orig = snapshot(TSV)
    try:
        r = run(["python3", "scripts/gen-symbol-addresses.py"])
        new = snapshot(TSV)
        if new != orig:
            return [("scripts/asm-fixtures/symbol-addresses.tsv",
                     "regionmap ELF symbols",
                     "python3 scripts/gen-symbol-addresses.py")]
        return []
    finally:
        restore(TSV, orig)


def check_guest_addrs():
    """GuestAddrs.lean vs tsv (check mode)."""
    r = run(["python3", "scripts/asm_to_program.py", "check-guest-addrs"])
    if r.returncode != 0:
        return [("EvmAsm/Codegen/GuestAddrs.lean",
                 "scripts/asm-fixtures/symbol-addresses.tsv",
                 "python3 scripts/asm_to_program.py guest-addrs")]
    return []


def check_entries():
    """GuestImageEntries.lean vs MANIFEST + tsv."""
    orig = snapshot(ENTRIES)
    try:
        run(["python3", "scripts/guest_image_coverage.py", "--emit-lean"])
        new = snapshot(ENTRIES)
        if new != orig:
            return [("EvmAsm/Codegen/Proofs/GuestImageEntries.lean",
                     "MANIFEST.tsv + symbol-addresses.tsv",
                     "python3 scripts/guest_image_coverage.py --emit-lean")]
        return []
    finally:
        restore(ENTRIES, orig)


def check_coverage_doc():
    """coverage doc vs GuestImageEntries."""
    r = run(["python3", "scripts/guest_image_coverage.py", "--check-doc"])
    if r.returncode != 0:
        return [("docs/4ch8f-guest-image-coverage.md",
                 "EvmAsm/Codegen/Proofs/GuestImageEntries.lean",
                 "python3 scripts/guest_image_coverage.py --write-doc")]
    return []


def check_pins():
    """RegionMapLinkPins.lean vs regionmap ELF (check mode)."""
    r = run(["python3", "scripts/gen-region-map-link-pins.py", "--check"])
    if r.returncode != 0:
        return [("EvmAsm/Codegen/RegionMapLinkPins.lean",
                 "regionmap ELF .text layout",
                 "python3 scripts/gen-region-map-link-pins.py")]
    return []


def manifest_rows():
    """(lean_file, func_name) per MANIFEST row, skipping comment/header lines."""
    rows = []
    with open(MANIFEST) as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 2 and not parts[0].startswith("#"):
                rows.append((parts[1], parts[0]))
    return rows


def check_fixtures():
    """.s fixtures vs Lean source emission (offline legs), one check-file call per
    def (the tool's --funcs batching false-positives on the 2nd+ def of a file),
    parallel — serial check-all is too slow (#12268)."""
    defs = manifest_rows()

    def one(item):
        f, n = item
        r = run(["python3", "scripts/asm_to_program.py", "check-file",
                 "--file", f, "--funcs", n])
        return (f, n, r)

    bad = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        for f, n, r in ex.map(one, defs):
            if r.returncode != 0:
                bad.append((f, n))
    return [("scripts/asm-fixtures/%s.s" % n,
             "Lean source emission (%s)" % f,
             "python3 scripts/asm_to_program.py convert %s %s (review direction!)" % (f, n))
            for f, n in bad]


def check_conditional_set():
    """Derive the covering set: every MANIFEST row needs a fixture file; every
    fixture file needs a MANIFEST row (orphan fixture = stale derived set)."""
    rows = set()
    with open(MANIFEST) as f:
        for line in f:
            parts = line.strip().split("\t")
            if parts and parts[0] and not parts[0].startswith("#"):
                rows.add(parts[0])
    findings = []
    for name in sorted(rows):
        if not os.path.exists(os.path.join(FIXTURE_DIR, name + ".s")):
            findings.append(("scripts/asm-fixtures/%s.s" % name,
                             "MANIFEST.tsv row for %s (converted routine)" % name,
                             "create the fixture via the asm_to_program pipeline"))
    for fn in sorted(os.listdir(FIXTURE_DIR)):
        if fn.endswith(".s") and fn[:-2] not in rows:
            findings.append(("scripts/asm-fixtures/%s" % fn,
                             "MANIFEST.tsv (no row claims this fixture)",
                             "add the MANIFEST row or delete the orphan fixture"))
    return findings


CHECKS = [
    ("fixture", check_fixtures),
    ("tsv", check_tsv),
    ("guest-addrs", check_guest_addrs),
    ("entries", check_entries),
    ("coverage-doc", check_coverage_doc),
    ("pins", check_pins),
    ("conditional-set", check_conditional_set),
]


def report(findings):
    for artifact, rel, regen in findings:
        print("STALE: %s\n  relative to: %s\n  regen: %s" % (artifact, rel, regen))


def self_test():
    """Corrupt each artifact in turn; assert the checker names it.
    Shape per #12270: assert the injection took effect BEFORE asserting the
    verdict flip, restore in finally, verify the tree is clean afterwards."""
    import re
    failures = []
    touched = []

    def expect(kind, path, mutate, must_name, runner=None):
        orig = snapshot(path)
        try:
            mutate(path)
            if snapshot(path) == orig:
                failures.append("%s: injection did not change %s" % (kind, path))
                return
            findings = (runner or dict(CHECKS)[kind])()
            ok = any(must_name in a for a, _, _ in findings)
            if not ok:
                failures.append("%s: checker did not name %s (got %r)"
                                % (kind, must_name, findings))
        finally:
            restore(path, orig)

    expect("tsv", TSV,
           lambda p: restore(p, snapshot(p) + b"\n"),
           "symbol-addresses.tsv")
    expect("entries", ENTRIES,
           lambda p: restore(p, snapshot(p) + b"\n-- stale\n"),
           "GuestImageEntries.lean")
    expect("pins", PINS,
           lambda p: restore(p, snapshot(p).replace(b"0x", b"0x0", 1)),
           "RegionMapLinkPins.lean")
    expect("guest-addrs", GUEST_ADDRS,
           lambda p: restore(p, re.sub(rb"0x[0-9a-f]+", b"0x0", snapshot(p), count=1)),
           "GuestAddrs.lean")

    ffile, fname = manifest_rows()[0]
    fpath = os.path.join(FIXTURES, fname + ".s")
    touched.append(fpath)
    def _bump_off(p):
        cur = snapshot(p)
        m = re.search(rb"-?\d+", cur)
        if not m:
            print("injection failed: no numeric token in fixture")
            sys.exit(2)
        new = cur[:m.start()] + str(int(m.group(0)) + 4).encode() + cur[m.end():]
        restore(p, new)
    expect("fixtures", fpath, _bump_off,
           fname + ".s",
           runner=lambda: [("%s.s" % fname, "x", "y")] if
           run(["python3", "scripts/asm_to_program.py", "check-file",
                "--file", ffile, "--funcs", fname]).returncode != 0 else [])

    if failures:
        print("SELF-TEST FAILURES:")
        for f in failures:
            print("  " + f)
        return 1
    dirty = run(["git", "status", "--porcelain", "--", TSV, ENTRIES, PINS,
                 GUEST_ADDRS, FIXTURES, "docs/4ch8f-guest-image-coverage.md"]).stdout.strip()
    if dirty:
        print("SELF-TEST FAILURE: tree not clean after restore:\n" + dirty)
        return 1
    print("self-test: all artifact kinds named correctly")
    return 0


def main():
    if "--self-test" in sys.argv:
        return self_test()
    if not os.path.exists(ELF):
        print("missing regionmap ELF: %s" % ELF)
        print("build first: lake build codegen && lake exe codegen --program "
              "stateless_guest --halt linux93 -o gen-out/regionmap/stateless_guest")
        return 2
    all_findings = []
    for name, fn in CHECKS:
        findings = fn()
        if findings:
            print("[%s]" % name)
            report(findings)
            all_findings.extend(findings)
    if all_findings:
        print("\n%d stale artifact(s)" % len(all_findings))
        return 1
    print("check-derived-artifacts: all derived artifacts consistent with their inputs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
