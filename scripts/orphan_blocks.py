#!/usr/bin/env python3
"""
orphan_blocks.py — detect basic blocks with no incoming edge (#12259).

Defect class: #12254 (lost beqz-a0 → orphaned status-0 block). Invisible to
source review because the defect is a *missing* branch.

Method (same instrument that pinned #12254): CFG over the *linked* guest ELF
objdump — not per-function Lean-string fragments. Edges do not respect
function boundaries (shared fail epilogues get incoming from other functions);
fragment analysis false-orphans them.

Block starts = named symbols in .text + first insn after unconditional j/ret
Incoming   = branch/jump targets + sequential fallthrough (except after
             unconditional j / ret / jalr)
Flag       = block starts that are not function/symbol entries and have
             zero incoming

Scope (first half only): orphaned blocks. Does NOT detect misaimed edges that
land mid-sequence (#12256) — see PR body.

Usage:
  python3 scripts/orphan_blocks.py                  # enforce vs snapshot
  python3 scripts/orphan_blocks.py --self-test      # synthetic + bucket self-tests
  python3 scripts/orphan_blocks.py --report         # print orphans, exit 0
  python3 scripts/orphan_blocks.py --update-snapshot
  python3 scripts/orphan_blocks.py --elf PATH       # override guest ELF

Snapshot buckets (#12264 option 2): scripts/orphan-blocks-expected.txt has
machine-parsed ``[baseline]`` and ``[known-open]`` sections. Known-open rows
require ``issue=<NNNN>``, are reported on every green run, and must not be
promoted into baseline without fixing the defect.
"""
from __future__ import annotations

import argparse
import collections
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXPECTED = ROOT / "scripts" / "orphan-blocks-expected.txt"
SYNTHETIC = ROOT / "scripts" / "orphan-blocks-synthetic.s"
DEFAULT_ELF = ROOT / "gen-out" / "regionmap" / "stateless_guest.elf"
AS = "riscv64-unknown-elf-as"
OBJDUMP = "riscv64-unknown-elf-objdump"
NM = "riscv64-unknown-elf-nm"

SECTION_BASELINE = "[baseline]"
SECTION_KNOWN_OPEN = "[known-open]"
ISSUE_RE = re.compile(r"^issue=(\d+)$")


def die(msg: str, code: int = 1) -> None:
    print(f"orphan_blocks: {msg}", file=sys.stderr)
    raise SystemExit(code)


def shutil_which(cmd: str) -> str | None:
    from shutil import which

    return which(cmd)


def parse_objdump(ofile: pathlib.Path) -> tuple[list[tuple[int, str, str, str]], dict[str, int]]:
    dump = subprocess.check_output([OBJDUMP, "-d", str(ofile)], text=True)
    instrs: list[tuple[int, str, str, str]] = []
    for line in dump.splitlines():
        m = re.match(r"\s*([0-9a-f]+):\s+[0-9a-f]+\s+(\S+)(?:\s+(.*))?", line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        op = m.group(2)
        rest = (m.group(3) or "").strip()
        instrs.append((addr, op, rest, line.strip()))

    nm = subprocess.check_output([NM, str(ofile)], text=True)
    sym_addrs: dict[str, int] = {}
    for line in nm.splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[1] in ("t", "T"):
            # Prefer the first binding if duplicates appear.
            sym_addrs.setdefault(parts[2], int(parts[0], 16))
    return instrs, sym_addrs


def parse_target(rest: str) -> int | None:
    # Objdump address width shrinks with object size: linked ELF uses 8+ hex
    # digits; a small assembled blob prints `beqz a0,50 <...>` (2 digits).
    m = re.search(r"(?:^|[\s,])([0-9a-f]{2,})(?:\s*<|$)", rest)
    return int(m.group(1), 16) if m else None


def is_uncond_jump(op: str, rest: str) -> bool:
    return op in ("j", "c.j") or (
        op == "jal" and (rest.startswith("zero") or rest.startswith("x0"))
    )


def is_ret_like(op: str, rest: str) -> bool:
    if op in ("ret", "c.jr"):
        return True
    if op == "jalr":
        dest = rest.split(",")[0].strip()
        return dest not in ("ra", "x1")
    return False


def assemble_synthetic(name: str, body: str, work: pathlib.Path) -> pathlib.Path:
    if not re.search(rf"^{re.escape(name)}:", body, re.M):
        body = f"{name}:\n{body}"
    full = f".option norvc\n.section .text\n.globl {name}\n{body}\n"
    sfile = work / f"{name}.s"
    ofile = work / f"{name}.o"
    sfile.write_text(full)
    r = subprocess.run(
        [AS, "--keep-locals", "-o", str(ofile), str(sfile)],
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        die(f"synthetic assemble failed: {r.stderr.strip() or 'error'}")
    return ofile


def analyze_text(
    instrs: list[tuple[int, str, str, str]],
    sym_addrs: dict[str, int],
    *,
    text_lo: int | None = None,
    text_hi: int | None = None,
    entry_names: set[str] | None = None,
) -> list[dict]:
    """CFG orphan scan over a contiguous instruction range.

    Every text symbol in range is an entry (never an orphan). Cross-symbol
    edges count — shared fail epilogues are reachable from other functions.
    """
    if not instrs:
        return []
    if text_lo is None:
        text_lo = instrs[0][0]
    if text_hi is None:
        text_hi = instrs[-1][0] + 4
    instrs = [x for x in instrs if text_lo <= x[0] < text_hi]
    if not instrs:
        return []

    # Entries: all text symbols in range (function starts + named labels gas kept).
    entries: dict[int, str] = {}
    for s, a in sym_addrs.items():
        if text_lo <= a < text_hi:
            if entry_names is not None and s not in entry_names and not s.startswith("L"):
                # When restricting to a synthetic fixture, only the named entries.
                if s not in entry_names:
                    continue
            entries[a] = s

    if entry_names is not None:
        for s in entry_names:
            if s in sym_addrs and text_lo <= sym_addrs[s] < text_hi:
                entries[sym_addrs[s]] = s

    if not entries:
        # Fall back: treat first insn as sole entry.
        entries[instrs[0][0]] = entry_names.pop() if entry_names else "_start"

    entry_addrs = set(entries)
    label_at = dict(entries)

    incoming: dict[int, set[int]] = collections.defaultdict(set)
    block_starts: set[int] = set(entry_addrs)

    for i, (addr, op, rest, _raw) in enumerate(instrs):
        next_addr = instrs[i + 1][0] if i + 1 < len(instrs) else None
        uncond = is_uncond_jump(op, rest)
        retish = is_ret_like(op, rest)

        if (uncond or op in ("ret", "c.jr")) and next_addr is not None:
            block_starts.add(next_addr)

        is_ctrl = (
            op.startswith("b")
            or op in ("j", "jal", "c.j")
            or op.startswith("c.b")
            or op.startswith("c.j")
        )
        t = parse_target(rest) if is_ctrl else None
        if t is not None and text_lo <= t < text_hi:
            # jal ra, external-or-local callee: still a control transfer TO t when
            # t is inside the scanned range (same-image call). Count it.
            if op == "jal" and (rest.startswith("ra") or rest.split(",")[0].strip() == "ra"):
                # Call to a function entry — marks the callee entry as reached,
                # which entries already are; do not treat as local block edge
                # into the middle of a function unless t is not an entry.
                incoming[t].add(addr)
                block_starts.add(t)
            else:
                incoming[t].add(addr)
                block_starts.add(t)

        if next_addr is not None and not (uncond or retish or op == "jalr"):
            incoming[next_addr].add(addr)

    # Owning function: nearest text symbol at or before addr whose name does
    # not look like a local .L label (nm strips the dot → leading L).
    entry_ordered = sorted(
        (a, s) for a, s in entries.items() if not s.startswith("L") and not s.startswith(".")
    )
    if not entry_ordered:
        entry_ordered = sorted(entries.items())

    def owning_fn(addr: int) -> tuple[str, int]:
        owner_a, owner_s = entry_ordered[0]
        for a, s in entry_ordered:
            if a <= addr:
                owner_a, owner_s = a, s
            else:
                break
        return owner_s, owner_a

    orphans: list[dict] = []
    used_stamps: dict[str, int] = collections.defaultdict(int)
    for b in sorted(block_starts):
        if b in entry_addrs:
            continue
        if incoming.get(b):
            continue
        owner, owner_base = owning_fn(b)
        at = [x for x in instrs if x[0] >= b][:4]
        preview = "; ".join(x[3].split(":")[-1].strip() for x in at[:2]) if at else ""
        # Stable stamp for snapshot keys (survives address drift across regenerations).
        stamp = None
        store = None
        for _a, op, rest, raw in at:
            m = re.match(r"(\w+),(-?\d+)$", rest)
            if op == "li" and m and stamp is None:
                stamp = f"li_{m.group(1)}_{m.group(2)}"
            ms = re.search(r"#\s*[0-9a-f]+\s+<([^>+]+)>", raw)
            if ms and store is None:
                store = ms.group(1)
            if op == "ret" and stamp is None:
                stamp = "ret_dead"
        if stamp is None and store is not None:
            stamp = f"la_{store}"
        if stamp is None:
            stamp = f"+{b - owner_base:#x}"
        # Disambiguate duplicate stamps inside the same function (e.g. two
        # derive blocks both `la cahsr_code_length`).
        base_stamp = stamp
        used_stamps[f"{owner}:{base_stamp}"] += 1
        n = used_stamps[f"{owner}:{base_stamp}"]
        if n > 1:
            stamp = f"{base_stamp}#{n}"
        orphans.append(
            {
                "fn": owner,
                "label": stamp,
                "stamp": stamp,
                "store": store,
                "offset": b - owner_base,
                "addr": b,
                "preview": preview,
            }
        )
    return orphans


def analyze_object(ofile: pathlib.Path, fn: str) -> list[dict]:
    """Single-function / synthetic analysis."""
    instrs, sym_addrs = parse_objdump(ofile)
    if fn not in sym_addrs:
        return []
    start = sym_addrs[fn]
    # End at next non-local symbol after fn, else end of dump.
    after = sorted(a for s, a in sym_addrs.items() if a > start and not s.startswith("L"))
    end = after[0] if after else (instrs[-1][0] + 4 if instrs else start)
    return analyze_text(
        instrs,
        sym_addrs,
        text_lo=start,
        text_hi=end,
        entry_names={fn},
    )


def analyze_linked_elf(elf: pathlib.Path) -> list[dict]:
    if not elf.is_file():
        die(f"missing linked guest ELF: {elf} (build/link first)")
    instrs, sym_addrs = parse_objdump(elf)
    if not instrs:
        die(f"no .text instructions in {elf}")
    return analyze_text(instrs, sym_addrs)


def orphan_key(o: dict) -> str:
    return f"{o['fn']}:{o.get('stamp') or o['label']}"


def format_snapshot(orphans: list[dict]) -> str:
    """Machine-oriented dump. Prefer the hand-annotated expected file for CI."""
    lines = [
        "# GENERATED — prefer the committed annotated baseline in",
        "# scripts/orphan-blocks-expected.txt (decidability groups A/B/C).",
        "# Format: fn:stamp",
        "#",
    ]
    if not orphans:
        lines.append("SENTINEL:gate-active")
    else:
        for o in sorted(orphans, key=orphan_key):
            lines.append(f"{orphan_key(o)}  # {o['preview'].replace(chr(9), ' ')[:60]}")
    lines.append("")
    return "\n".join(lines)


def load_expected(
    path: pathlib.Path = EXPECTED,
) -> tuple[set[str], dict[str, str]]:
    """Return (baseline_keys, known_open key→issue).

    Sections ``[baseline]`` and ``[known-open]`` are required structural markers
    (not comments). Known-open rows must be ``fn:stamp`` + ``issue=<NNNN>``.
    """
    if not path.is_file():
        die(f"missing committed snapshot: {path}")
    if path.stat().st_size == 0:
        die(f"committed snapshot is empty: {path}")

    section: str | None = None
    baseline: set[str] = set()
    known_open: dict[str, str] = {}
    saw_baseline = False
    saw_known = False

    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        if s == SECTION_BASELINE:
            section = "baseline"
            saw_baseline = True
            continue
        if s == SECTION_KNOWN_OPEN:
            section = "known-open"
            saw_known = True
            continue
        if s.startswith("[") and s.endswith("]"):
            die(f"{path}:{lineno}: unknown section {s!r} (want {SECTION_BASELINE} / {SECTION_KNOWN_OPEN})")
        if section is None:
            die(
                f"{path}:{lineno}: entry before {SECTION_BASELINE} / {SECTION_KNOWN_OPEN}: {s!r}"
            )

        if section == "baseline":
            key = s.split()[0]
            if key in baseline or key in known_open:
                die(f"{path}:{lineno}: duplicate key {key}")
            baseline.add(key)
            continue

        # known-open: key + issue=<NNNN> (tab or space separated)
        parts = s.split()
        if len(parts) < 2:
            die(
                f"{path}:{lineno}: known-open entry requires issue=<NNNN> "
                f"(got {s!r}) — file an issue before tolerating an orphan"
            )
        key = parts[0]
        issue_tok = parts[1]
        m = ISSUE_RE.match(issue_tok)
        if m is None:
            die(
                f"{path}:{lineno}: known-open entry must use issue=<NNNN> "
                f"(got {issue_tok!r} on {key})"
            )
        if key in baseline or key in known_open:
            die(f"{path}:{lineno}: duplicate key {key}")
        known_open[key] = m.group(1)

    if not saw_baseline or not saw_known:
        die(
            f"{path}: both {SECTION_BASELINE} and {SECTION_KNOWN_OPEN} "
            "section headers are required"
        )
    if not baseline and not known_open:
        die("committed snapshot has no entries (vacuous success forbidden)")
    if not baseline:
        die(f"{path}: {SECTION_BASELINE} section is empty (vacuous baseline forbidden)")
    return baseline, known_open


def classify(
    actual: set[str], baseline: set[str], known_open: dict[str, str]
) -> tuple[list[str], list[str], list[tuple[str, str]], list[str]]:
    """Return (new, missing_baseline, present_known_open, absent_known_open).

    ``new`` = actual keys in neither bucket (gate failure).
    ``missing_baseline`` = baseline keys not observed (gate failure).
    ``present_known_open`` = (key, issue) pairs observed (must be reported).
    ``absent_known_open`` = known-open keys not observed (informational; still OK —
    the defect may have been fixed; operators should delete the row).
    """
    allowed = baseline | set(known_open)
    new = sorted(actual - allowed)
    missing_baseline = sorted(baseline - actual)
    present_ko = sorted(
        ((k, known_open[k]) for k in known_open if k in actual), key=lambda x: x[0]
    )
    absent_ko = sorted(k for k in known_open if k not in actual)
    return new, missing_baseline, present_ko, absent_ko


def enforce(
    actual: set[str],
    baseline: set[str],
    known_open: dict[str, str],
    *,
    stream=sys.stderr,
) -> int:
    """Exit status: 0 if only baseline/known-open; 1 on new or missing baseline.

    Always prints present known-open rows with their issue numbers (even on
    success) so the bucket cannot rot silently.
    """
    new, missing, present_ko, absent_ko = classify(actual, baseline, known_open)

    if present_ko:
        print("orphan_blocks: known-open orphans present (tracked defects):", file=stream)
        for k, issue in present_ko:
            print(f"  {k}  issue=#{issue}", file=stream)
    if absent_ko:
        print(
            "orphan_blocks: known-open entries not observed "
            "(remove from [known-open] if the defect is fixed):",
            file=stream,
        )
        for k in absent_ko:
            print(f"  {k}  issue=#{known_open[k]}", file=stream)

    if new or missing:
        print("orphan_blocks: snapshot mismatch", file=stream)
        if new:
            print("  NEW orphans (not in [baseline] or [known-open]):", file=stream)
            for k in new:
                print(f"    {k}", file=stream)
        if missing:
            print("  MISSING baseline orphans (in [baseline], not found):", file=stream)
            for k in missing:
                print(f"    {k}", file=stream)
        print(
            "  update scripts/orphan-blocks-expected.txt in the same PR "
            "after confirming the CFG change is intentional "
            "(known-open rows need issue=<NNNN>)",
            file=stream,
        )
        return 1
    return 0


def run_self_test(work: pathlib.Path) -> None:
    """Synthetic CFG flip + bucket discipline (unknown fails; known-open reports)."""
    if not SYNTHETIC.is_file():
        die(f"missing synthetic fixture: {SYNTHETIC}")
    dirty = SYNTHETIC.read_text(encoding="utf-8")
    ofile = assemble_synthetic("orphan_synth_dirty", dirty, work)
    dirty_orphans = analyze_object(ofile, "orphan_synth_dirty")
    if not dirty_orphans:
        die("self-test FAILED: planted orphan was NOT reported (gate cannot fail)")

    clean = re.sub(
        r"\n\s*j\s+\.Lorphan_alive\n.*?(?=\.Lorphan_alive:)",
        "\n",
        dirty,
        count=1,
        flags=re.S,
    )
    ofile2 = assemble_synthetic("orphan_synth_clean", clean, work)
    clean_orphans = analyze_object(ofile2, "orphan_synth_clean")
    if len(dirty_orphans) <= len(clean_orphans):
        print(
            f"self-test FAILED: verdict did not flip "
            f"(dirty={len(dirty_orphans)} clean={len(clean_orphans)})",
            file=sys.stderr,
        )
        raise SystemExit(1)

    planted = orphan_key(dirty_orphans[0])

    # Bucket self-test: unknown orphan must fail; known-open must pass AND report.
    snap = work / "bucket-expected.txt"
    # Minimal baseline so the file is non-vacuous; use a sentinel key that will
    # not appear in the synthetic object (missing-baseline is OK to avoid here
    # by putting a fake baseline key that we also inject into `actual` for the
    # known-open leg only via classify directly).
    snap.write_text(
        f"{SECTION_BASELINE}\n"
        f"_self_test_baseline:li_a0_0\n"
        f"\n"
        f"{SECTION_KNOWN_OPEN}\n"
        f"{planted}\tissue=12273\n",
        encoding="utf-8",
    )
    baseline, known_open = load_expected(snap)
    if planted not in known_open or known_open[planted] != "12273":
        die("self-test FAILED: known-open parse did not keep planted key + issue")

    # Refuse known-open without issue=
    bad = work / "bad-known-open.txt"
    bad.write_text(
        f"{SECTION_BASELINE}\n_self_test_baseline:li_a0_0\n\n"
        f"{SECTION_KNOWN_OPEN}\n{planted}\n",
        encoding="utf-8",
    )
    import contextlib
    import io

    err = io.StringIO()
    with contextlib.redirect_stderr(err):
        try:
            load_expected(bad)
            accepted = True
        except SystemExit as e:
            accepted = e.code == 0
    if accepted:
        die("self-test FAILED: known-open without issue= was accepted")
    if "issue=<NNNN>" not in err.getvalue():
        die("self-test FAILED: refuse message did not demand issue=<NNNN>")

    actual_dirty = {orphan_key(o) for o in dirty_orphans}
    # Unknown: planted not in either bucket
    new, _m, _p, _a = classify(actual_dirty, {"_self_test_baseline:li_a0_0"}, {})
    if planted not in new:
        die(
            f"self-test FAILED: unknown planted orphan {planted} was not classified NEW"
        )

    # Known-open: planted listed → not NEW; enforce reports it
    buf = io.StringIO()
    # Supply baseline key as present so missing-baseline does not fire.
    actual_ok = set(actual_dirty) | {"_self_test_baseline:li_a0_0"}
    rc = enforce(actual_ok, baseline, known_open, stream=buf)
    report = buf.getvalue()
    if rc != 0:
        die(f"self-test FAILED: known-open planted orphan should pass (rc={rc})")
    if "known-open orphans present" not in report or planted not in report:
        die(
            "self-test FAILED: known-open pass did not REPORT the entry "
            f"(report={report!r})"
        )
    if "issue=#12273" not in report:
        die("self-test FAILED: known-open report missing issue=#12273")

    # Load the real committed snapshot (structure check).
    real_base, real_ko = load_expected(EXPECTED)
    if "eip7702_authority_asof:li_t0_2" not in real_ko:
        die("self-test FAILED: committed [known-open] missing eip7702 li_t0_2")

    print(
        f"orphan_blocks self-test: OK "
        f"(dirty reported {len(dirty_orphans)} orphan(s); "
        f"clean {len(clean_orphans)}; verdict flipped; "
        f"unknown→NEW; known-open→pass+report; "
        f"committed baseline={len(real_base)} known-open={len(real_ko)})"
    )


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--report", action="store_true", help="print orphans; exit 0")
    ap.add_argument("--update-snapshot", action="store_true")
    ap.add_argument("--count-only", action="store_true", help="print orphan count and keys")
    ap.add_argument("--elf", type=pathlib.Path, default=DEFAULT_ELF, help="linked guest ELF")
    args = ap.parse_args()

    if not pathlib.Path(f"/usr/bin/{AS}").exists() and not shutil_which(AS):
        die(f"{AS} not found (required for assemble+objdump CFG audit)")

    with tempfile.TemporaryDirectory(prefix="orphan-blocks-") as td:
        work = pathlib.Path(td)
        if args.self_test:
            run_self_test(work)
            return

        orphans = analyze_linked_elf(args.elf)
        keys = {orphan_key(o) for o in orphans}

        if args.update_snapshot:
            # Writes a flat generated dump for debugging only — the committed
            # annotated file with [baseline]/[known-open] is hand-maintained.
            EXPECTED.write_text(format_snapshot(orphans), encoding="utf-8")
            print(
                f"orphan_blocks: wrote {EXPECTED} ({len(orphans)} orphan(s)) — "
                "REFORMAT into [baseline]/[known-open] before committing"
            )
            return

        if args.count_only or args.report:
            print(f"orphan_blocks: {len(orphans)} orphan(s) on linked ELF {args.elf}")
            for o in sorted(orphans, key=orphan_key):
                print(f"  {orphan_key(o)}  # {o['preview'][:80]}")
            return

        baseline, known_open = load_expected()
        rc = enforce(keys, baseline, known_open, stream=sys.stderr)
        if rc != 0:
            raise SystemExit(rc)
        print(
            f"orphan_blocks: OK ({len(orphans)} orphan(s); "
            f"baseline={len(baseline)} known-open={len(known_open)})"
        )


if __name__ == "__main__":
    main()
