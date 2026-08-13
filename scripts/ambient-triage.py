#!/usr/bin/env python3
"""ambient-triage.py — partition the `--shape` model-only bucket by liftability (#12244 ask 3).

Why this exists
---------------
#12244 asked to "sweep the bucket": take the model-only symbols whose `Fn` has a
proven `.Spec` and lift + row them in in-degree order. Doing the first three by
hand (#12283) showed the bucket is NOT uniform, and that the thing which decides
the cost is a single syntactic property of the leaf's own contract:

    Does the `Fn`'s `post` PIN the ambient assertion?

Every flat-lift adapter in `EvmAsm/Rv64/SAsm/FnFlat.lean` demands it:

    Fn.retSpecFlat         needs  hpostEmp : ... f.post rf' ws' A → A = empAssertion
    Fn.retSpecFlatAmbient  needs  hpostAmb : ... f.post rf' ws' A' → A' = A

Neither is dischargeable unless the post itself constrains its ambient argument,
because that is the only way the fact survives out of the existentially-quantified
`asrtOf` in `Fn.retSpec`'s conclusion. So:

  * post pins the ambient   ->  MECHANICAL. Mirror `u256AddBeFlat_spec`; ~120 lines
                                of separation-logic plumbing, no new insight.
  * post ignores it (`fun _ ws _ =>`)
                            ->  CONTRACT CHANGE FIRST. The leaf's `pre` and `post`
                                must both pin the ambient before any adapter
                                applies (post can only discharge the conjunct by
                                reading it off the pre; the reach relation threads
                                `A` unchanged). That edits an existing definition
                                and re-proves its `vcgen` post case, so it is only
                                safe when the `Fn` has no external consumers —
                                which this script also reports.

An ambient-agnostic post looks strictly MORE general and is strictly LESS usable.
That inversion is the whole finding, and it is why "lift in in-degree order" is the
wrong queue: in-degree tells you the value, this tells you the cost.

Third outcome, found the same way: some symbols in the bucket need NO lift at all,
because a flat triple already exists in a sibling module and only the shape
classifier missed it (it resolves one theorem per symbol). `u256_is_zero` was one.
So the script also greps for an existing `cpsTripleWithin` mentioning the symbol's
anchor and flags those as ALREADY-FLAT — check those before writing any proof.

Usage:
  python3 scripts/ambient-triage.py            # summary + per-symbol table
  python3 scripts/ambient-triage.py --verbose   # also print each post it parsed
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERBOSE = "--verbose" in sys.argv


def model_only_rows() -> list[tuple[str, str]]:
    """(symbol, theorem) for every row the shape classifier calls model-only."""
    out = subprocess.run(
        [sys.executable, "scripts/proof-frontier.py", "--shape"],
        cwd=ROOT, capture_output=True, text=True,
    ).stdout
    rows = []
    for line in out.splitlines():
        parts = line.split()
        # data rows look like: <symbol> model-only <theorem> <why...>
        if len(parts) >= 3 and parts[1] == "model-only" and not line.startswith(" "):
            rows.append((parts[0], parts[2]))
    return rows


def lean_files() -> list[Path]:
    return sorted(ROOT.joinpath("EvmAsm").rglob("*.lean"))


FILES = lean_files()
TEXT = {p: p.read_text(encoding="utf-8", errors="replace") for p in FILES}


def fn_candidates(theorem: str) -> list[str]:
    """Plausible `Fn` definition names for a `*_spec` theorem."""
    base = re.sub(r"_spec$", "", theorem)
    cands = [base]
    if not base.endswith("Fn"):
        cands.append(base + "Fn")
    return cands


def find_fn_block(fn_name: str) -> tuple[Path, str] | None:
    """The source of `def <fn_name> ... : Fn where` up to the next top-level def."""
    pat = re.compile(rf"^def {re.escape(fn_name)}\b", re.M)
    for path, text in TEXT.items():
        m = pat.search(text)
        if not m:
            continue
        rest = text[m.start():]
        nxt = re.search(r"\n(?=(?:def|theorem|@\[|private|/--|end)\s)", rest[1:])
        block = rest[: nxt.start() + 1] if nxt else rest[:4000]
        return path, block
    return None


POST_RE = re.compile(r"post\s*:=\s*(\S[^\n]*(?:\n(?![ ]{0,2}\w+\s*:=)[^\n]*)*)")
DEF_RE_CACHE: dict[str, str | None] = {}


def resolve_reach_def(name: str) -> str | None:
    """Body of `def <name> ... : Reach := fun ...`, if it exists.

    Needed because a `post` is often a NAMED `Reach` rather than an inline `fun`:
    `u256AddBeFn`'s is `post := u256AddBePost aPtr bPtr outPtr aBytes bBytes orig`.
    The self-test caught this — the very template this script points people at was
    classified `unparsed` until the indirection was followed.
    """
    if name in DEF_RE_CACHE:
        return DEF_RE_CACHE[name]
    # ⚠️ The header can span several lines — `def u256AddBePost (a b c : Word)\n
    # (d e f : List (BitVec 8)) : Reach :=` — so do NOT try to reach `:=` with a
    # single-line pattern. Anchor on the `def`, then take everything after the
    # first `:=` that follows. An earlier `[^\n]*:=` version silently matched
    # nothing and the self-test reported the template itself as `unparsed`.
    pat = re.compile(rf"^def {re.escape(name)}\b", re.M)
    body = None
    for text in TEXT.values():
        m = pat.search(text)
        if not m:
            continue
        after = text[m.end():]
        eq = after.find(":=")
        if eq == -1:
            continue
        rest = after[eq + 2:]
        nxt = re.search(r"\n(?=(?:def|theorem|@\[|private|/--|end)\s)", rest)
        body = rest[: nxt.start()] if nxt else rest[:2000]
        break
    DEF_RE_CACHE[name] = body
    return body


def classify_post(block: str) -> tuple[str, str]:
    """('pins'|'agnostic'|'unparsed', the post source we looked at)."""
    m = POST_RE.search(block)
    if not m:
        return "unparsed", ""
    post = m.group(1)
    if not post.lstrip().startswith("fun"):
        # Named `Reach` — follow one level of indirection.
        head = re.match(r"([A-Za-z_][A-Za-z0-9_.]*)", post.strip())
        if head:
            resolved = resolve_reach_def(head.group(1))
            if resolved:
                post = resolved
    # Binders of the leading `fun a b c =>`: third is the ambient.
    # `lstrip()` matters: a resolved named `Reach` body begins with a newline, and
    # `re.match` anchors at position 0.
    post = post.lstrip()
    b = re.match(r"fun\s+(\S+)\s+(\S+)\s+(\S+)\s*=>", post)
    if not b:
        return "unparsed", post
    ambient = b.group(3)
    if ambient == "_":
        return "agnostic", post
    # Named ambient: it pins only if the body actually constrains it.
    if re.search(rf"\b{re.escape(ambient)}\s*=", post):
        return "pins", post
    return "agnostic", post


def already_flat(symbol: str) -> str | None:
    """A file with both a cpsTripleWithin and this symbol's GuestAddrs anchor."""
    anchor = f"GuestAddrs.{symbol}"
    for path, text in TEXT.items():
        if anchor in text and "cpsTripleWithin" in text:
            # crude but effective: the anchor and a triple in the same module
            if re.search(r"theorem\s+\w+[^\n]*\n(?:[^\n]*\n){0,12}?[^\n]*cpsTripleWithin", text):
                return str(path.relative_to(ROOT))
    return None


GUESTADDRS = ROOT / "EvmAsm/Codegen/GuestAddrs.lean"
ENTRIES = ROOT / "EvmAsm/Codegen/Proofs/GuestImageEntries.lean"
GA_TEXT = GUESTADDRS.read_text(encoding="utf-8", errors="replace") if GUESTADDRS.exists() else ""
EN_TEXT = ENTRIES.read_text(encoding="utf-8", errors="replace") if ENTRIES.exists() else ""


def anchored(symbol: str) -> bool:
    """Rowability's SECOND necessary condition, independent of liftability.

    A flat triple can only be anchored — and therefore only rowed — if the symbol
    has an address in `GuestAddrs.lean` AND a `(GuestAddrs.<sym>, <sym>_prog)`
    pair in `GuestImageEntries.lean`. Liftability says the proof is cheap;
    this says the result would be a claim about the DEPLOYED image at all.

    Added after the first run of this script reported the four gas helpers
    (`log_data_gas`, `keccak256_word_gas`, `copy_word_gas`, `init_code_cost`) as
    MECHANICAL. They are mechanically liftable — but they have no `GuestAddrs`
    entry and in-degree 0, so no honest row can cite them and the lift buys
    nothing today. Conflating the two would have sent the next agent to write
    four unrowable proofs.
    """
    if not re.search(rf"^def {re.escape(symbol)}\b", GA_TEXT, re.M):
        return False
    return f"GuestAddrs.{symbol}," in EN_TEXT


def external_consumers(fn_name: str, home: Path) -> int:
    """How many OTHER files mention this `Fn` — a contract change's blast radius."""
    return sum(1 for p, t in TEXT.items() if p != home and fn_name in t)


def self_test() -> int:
    """Regression-test the classifier against cases whose truth was set BY HAND.

    #12283 proved these four out one at a time, before this script existed, so
    they are ground truth rather than the script's own output — which is the only
    kind of evidence a classifier like this can really carry (the #12240 lesson,
    after #12231 wrongly demoted five entries on a name heuristic).

    Expectations, and why each one is here:

      u256AddBeFn      pins      its post ends `A = (bytesRegion .. ** bytesRegion ..)`,
                                 so `hpostAmb` was dischargeable and the lift was
                                 mechanical — the template every harvest mirrors.
      u256FromU64BeFn  pins      ⚠️ ONLY because #12283 changed it. Its post was
                                 `fun _ ws _ => ws = u256FromU64Bytes v`, i.e.
                                 ambient-AGNOSTIC, and NEITHER adapter applied. If
                                 this ever reads `agnostic` again, someone reverted
                                 the pinning and the flat triple cannot be rebuilt.
      u256_is_zero     flat      needed NO lift: a flat triple already sat in
                                 `Codegen/Proofs/U256IsZeroSpec.lean` and only its
                                 `base` was unanchored. The `--shape` classifier
                                 called it model-only and was wrong.
      log_data_gas     unanchored  mechanically liftable, but no GuestAddrs address
                                 and no GuestImageEntries pair, so never rowable.
    """
    failures = []

    def check(name: str, got, want) -> None:
        ok = got == want
        print(f"  {'PASS' if ok else 'FAIL'}  {name}: got {got!r}, want {want!r}")
        if not ok:
            failures.append(name)

    print("ambient-triage --self-test (ground truth established by hand in #12283)\n")

    for fn, want in (("u256AddBeFn", "pins"), ("u256FromU64BeFn", "pins")):
        found = find_fn_block(fn)
        if not found:
            check(f"{fn} located", False, True)
            continue
        verdict, _ = classify_post(found[1])
        check(f"{fn} post", verdict, want)

    check("u256_is_zero anchored", anchored("u256_is_zero"), True)
    check("u256_is_zero already-flat", already_flat("u256_is_zero") is not None, True)
    check("log_data_gas anchored", anchored("log_data_gas"), False)

    print()
    if failures:
        print(f"ambient-triage --self-test: FAILED ({len(failures)}): {', '.join(failures)}")
        return 1
    print("ambient-triage --self-test: OK — classifier reproduces all hand-established verdicts.")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    rows = model_only_rows()
    if not rows:
        print("ambient-triage: no model-only rows reported — is proof-frontier.py --shape available?")
        return 1

    buckets: dict[str, list] = {"pins": [], "agnostic": [], "unparsed": [], "nofn": []}
    rowable_mech: list[str] = []
    unanchored: list[str] = []
    print(f"ambient-triage: {len(rows)} model-only symbols from proof-frontier.py --shape\n")
    print(f"{'symbol':<34}{'verdict':<14}{'anch':<6}{'Fn':<30}{'ext':>4}  note")
    print("-" * 114)

    for symbol, theorem in sorted(rows):
        found = None
        for cand in fn_candidates(theorem):
            found = find_fn_block(cand)
            if found:
                fn_name = cand
                break
        if not found:
            buckets["nofn"].append((symbol, theorem))
            print(f"{symbol:<34}{'NO-FN':<14}{'(' + theorem + ')':<30}{'-':>4}  could not locate `def … : Fn`")
            continue

        path, block = found
        verdict, post = classify_post(block)
        ext = external_consumers(fn_name, path)
        flat = already_flat(symbol)
        note = f"⭐ flat triple may already exist: {flat}" if flat else ""
        if verdict == "agnostic" and ext == 0:
            note = note or "contract change is SAFE (no external consumers)"
        elif verdict == "agnostic":
            note = note or f"contract change touches {ext} other file(s) — check first"
        buckets[verdict].append((symbol, fn_name, ext, flat))
        anc = anchored(symbol)
        if not anc:
            unanchored.append(symbol)
            note = note or "⛔ NOT ANCHORED — no GuestAddrs/GuestImageEntries pair, so NOT rowable"
        elif verdict == "pins" and not flat:
            rowable_mech.append(symbol)
        label = {"pins": "MECHANICAL", "agnostic": "CONTRACT-1ST", "unparsed": "READ"}[verdict]
        print(f"{symbol:<34}{label:<14}{('yes' if anc else 'NO'):<6}{fn_name:<30}{ext:>4}  {note}")
        if VERBOSE and post:
            print(f"    post := {' '.join(post.split())[:160]}")

    print("\n" + "=" * 60)
    print(f"  MECHANICAL   (post pins ambient)      : {len(buckets['pins'])}")
    print(f"  CONTRACT-1ST (post ignores ambient)   : {len(buckets['agnostic'])}")
    print(f"  READ         (post did not parse)     : {len(buckets['unparsed'])}")
    print(f"  NO-FN        (no `: Fn` def found)    : {len(buckets['nofn'])}")
    print("=" * 60)
    print(f"  of which NOT ANCHORED (never rowable): {len(unanchored)}")
    print("=" * 60)
    print("\n⭐ THE ACTUAL WORK QUEUE — MECHANICAL *and* anchored *and* no existing flat triple:")
    if rowable_mech:
        for s in rowable_mech:
            print(f"    {s}")
    else:
        print("    (none)")
    print("\nMechanical means: mirror `u256AddBeFlat_spec`")
    print("(EvmAsm/Codegen/Proofs/U256BeFlatTriples.lean); ~120 lines, no new insight.")
    print("CONTRACT-1ST needs the leaf's pre AND post pinned before any adapter")
    print("applies — cheap where ext = 0, a reviewable change otherwise.")
    print("NOT ANCHORED means liftable but unrowable: no GuestAddrs address and/or no")
    print("GuestImageEntries pair, so a triple about it is not a claim about the image.")
    print("Check every ⭐ before proving: the lift may already be unnecessary.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
