#!/usr/bin/env python3
"""callee-composition-queue.py — demand-ranked worklist for the in-image proof lanes (#12318).

WHAT IT ANSWERS
---------------
Per routine actually linked into the guest image:

  * control-flow shape (loop-free? indirect? accelerator call? how many instructions?)
  * its callees, resolved to guest symbols
  * whether every callee already has a registry row  -> STARTABLE by composition
  * whether any callee's row is a WEAK CONTRACT      -> demoted out of startable
  * which unrowed callee blocks the most routines    -> demand-queue input (#12035)
  * caller in-degree, from the image call graph and from the fixture call graph
  * whether the symbol is a named residual in `Progress/Obligations.lean`, and
    (optionally, from a fetched dump) in an open GitHub issue

⛔ WHY THIS DOES NOT USE scripts/shape-census.py
------------------------------------------------
That census parses the emitted `*Function : String` defs as assembly text, and it
is **structurally blind to every converted routine**, which is precisely the
population that can carry a row. A routine's `Function` string contains literal
asm only while it is UNCONVERTED:

    -- unconverted: asm text, census can read it
    def precompileSharedSelectPriceFunction : String :=
      "precompile_shared_select_price:\\n" ++
      "  la t0, precompile_shared_selector\\n  sd zero, 0(t0)\\n" ++ ...

    -- converted: no asm at all, just a label and a Program reference
    def secfEq32Function : String :=
      "secf_eq32:\\n" ++ emitProgram secfEq32_prog

Conversion is what earns a routine a Lean `Program`, hence a `guestImageEntries`
pairing, hence linkage. Measured on this tree: of 984 emitted `*Function` defs,
**565 parse to ZERO instructions**, and of the 449 linked symbols exactly **one**
has readable asm text.

⚠️ And a zero-instruction body is indistinguishable from a branch-free one — no
instructions means no branches — so the census files it as a "flat block". That is
why its flat-block figure reads 588: ~96% of that class is empty parses, not flat
routines. **Any shape claim about in-image routines taken from that tool is
unfounded**, including population figures derived from it. Two such figures were
in circulation and both were wrong; see the header of
`EvmAsm/Tests/GuestImageShapeDump.lean`.

So shape comes from the Lean `Program`s themselves, via that dump.

⛔ AND THE DUMP ITSELF WAS WRONG UNTIL #12318 (read this before quoting a number)
--------------------------------------------------------------------------------
`GuestImageShapeDump` graded a back-edge as "any negative-offset transfer". A
`jal`/`j` to a callee laid out at a LOWER address has a negative offset, so every
backward CALL read as a loop. 114 of 442 image entries were misgraded — including
`mpt_delete_walk_db`, whose whole body is one instruction (`j mpt_set_record_walk_db`)
and which this tool reported as loop-bearing. The loop-free population read **49**
when it is **163**, and the unrowed loop-free-with-calls lane this tool exists to
schedule read **3** when it is **93**.

The fix (back-edge = negative offset AND target inside the routine's own extent)
is corroborated by an INDEPENDENT measurement, not by inspection: `--self-test`
re-derives the back-edge grade from the `scripts/asm-fixtures/*.s` assembly text
and requires it to agree with the `Program`-level grade on every fixture-bearing
entry. Before the fix that check stood at 327/441; after it, 441/441.

REGENERATING THE INPUT
    lake build EvmAsm.Tests.GuestImageShapeDump
    lake env lean scripts/lean/GuestImageShapeDumpRun.lean > /tmp/shape.tsv
    python3 scripts/callee-composition-queue.py --tsv /tmp/shape.tsv

  ⚠️ `lake env lean` resolves the import from the built `.olean`, so WITHOUT the
  `lake build` first a source edit to the dump is silently ignored and you get the
  previous shape data. This script hard-fails on a 5-column (pre-#12318) dump
  rather than reading it, because a stale dump reproduces the misgrade above with
  no visible symptom.

OPTIONAL INPUT — open-issue residuals
    gh issue list --repo Verified-zkEVM/evm-asm --state open --limit 500 \
      --json number,title,body > /tmp/issues.json
    python3 scripts/callee-composition-queue.py --issues-json /tmp/issues.json

  Without it the open-issue column reads `?`, never `no`: this script does not
  reach the network on its own, and "I did not look" must not render as "absent".

⚠️ A ROW IS NOT A CONTRACT — THE TWO WEAK-CONTRACT PROXIES (#12318 follow-up)
-----------------------------------------------------------------------------
`startable` used to mean only "every callee carries a registry row". That reads as
"every callee is composable", and it is not the same claim. The counterexample,
found by review on #12799 and mechanically confirmed here:

    routine "header_extended_decode" .proven
        (some "header_extended_decode_u64_segment_spec_within")   -- field 9
    …four more rows, ALL citing that SAME theorem                 -- fields 10,11,17,18

FIVE `.proven` rows for one symbol, one theorem between them — a per-field u64
segment lemma replicated per field, with NO whole-routine triple anywhere. A caller
scored `startable` on the strength of five rows it cannot compose against. A
neighbouring row (`validate_header`) says outright "witness is the emit drift guard
only". So a callee is demoted from `startable` to `needs-read` when EITHER holds:

  RULE 1 (structure) — the symbol has ≥2 registry rows and every one of them cites
      the SAME theorem. One theorem cannot be the whole-routine contract for a
      symbol that needed N rows to describe itself; in practice it is a per-case or
      per-field lemma with the routine-level statement still missing.
  RULE 2 (name) — no row for the symbol cites a theorem whose name carries a
      whole-routine suffix. The suffix table is
      `check-registry-coverage.py`'s `WHOLE_ROUTINE_SPEC_SUFFIXES` — imported, not
      restated, and it is the same proxy that gate's tier-A split already uses.
      The #12568 namespace recovery is inherited with it: `pointDouble_spec` IS
      `secp256k1_point_double`'s whole-routine triple, with the prefix carried by
      the enclosing namespace, so a cited name recovered that way is NOT demoted.

⛔ BOTH ARE NAME/STRUCTURE PROXIES, NOT STATEMENT READS, and the output says so on
every row they touch. They are sound in exactly one direction: a demotion moves work
OUT of the confident bucket and into the one that means "read the statement", which
is the safe error. A PROMOTION on a proxy would not be, and none is offered — the
tool never moves a row INTO `startable`.

⚠️ Rule 2 fires on pre-convention contract names too. `u256Eq_spec`,
`frameBase_spec`, `secfBeToLeFlatEntry_spec` are believed to be genuine
whole-routine triples whose names predate `_spec_within`; the proxy cannot tell them
from a fragment, so their callers land in `needs-read`. That is the bucket working
as intended, not a claim that those rows are weak.

⚠️ AND `startable` STILL IS NOT `composable`, even after both rules. A callee's
REGISTER FRAME can block composition as effectively as a missing contract, and no
mechanical test here sees it: `sws_u32le` is `.proven`, total and ungated, yet its
`swsU32leScratch` surrenders `x29` — which its caller `extract_witness_state_section`
holds `state_off` in across a call. Rowed, ungated, whole-routine, and still not
composable as written. There is no third rule for this; there is only reading the
frame.

RELATED, AND DELIBERATELY NOT HANDLED HERE: #12797 is the mirror defect — a row's
`symbol` string does not pin the ADDRESS its `CodeReq` is over (three rows say
`rlp_walk_next`; all three are anchored at `GuestAddrs.rlp_walk_next_core`). That is
an address question, not a contract-shape question, and it is being fixed in
`check-registry-coverage.py`.

This is a TOOL (it computes an ordering for humans), not a gate: there is nothing
here that can be "violated", so it takes no `--strict` and needs no CI step. It
still carries a `--self-test`, because a worklist generator that cannot be
falsified is not worth much — the checks plant known-wrong inputs and require the
tool to catch them.

  ⚠️ `--self-test` needs `/tmp/shape.tsv`, so it has the same precondition as every
  other mode: `lake build EvmAsm.Tests.GuestImageShapeDump` FIRST, then
  `lake env lean scripts/lean/GuestImageShapeDumpRun.lean > /tmp/shape.tsv`. Without
  the build, `lake env lean` resolves the import from a stale `.olean`. A reviewer
  hit exactly this on #12790 and could not reproduce the agreement figures.
"""

from __future__ import annotations

import argparse
import glob
import importlib.util
import json
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.join(ROOT, "scripts")
GUESTADDRS = os.path.join(ROOT, "EvmAsm/Codegen/GuestAddrs.lean")
ROUTINES = os.path.join(ROOT, "EvmAsm/Progress/Routines.lean")
OBLIGATIONS = os.path.join(ROOT, "EvmAsm/Progress/Obligations.lean")
FIXTURES = os.path.join(ROOT, "scripts/asm-fixtures")


# ---------------------------------------------------------------------------
# sibling-script reuse
#
# `check-registry-coverage.py` owns the namespace-recovery rule (#12568):
# `pointDouble_spec` IS `secp256k1_point_double`'s triple, with the prefix carried
# by the enclosing namespace rather than the theorem name. Reimplementing that here
# would reproduce exactly the blind spot it was written to close, so it is imported.
# `proof-frontier.py` owns the fixture call-graph edges (a hand-rolled tail-call
# regex there produced the #11578 mis-annotation); imported for the same reason.
# ---------------------------------------------------------------------------
def _load(mod_name: str, filename: str):
    path = os.path.join(SCRIPTS, filename)
    spec = importlib.util.spec_from_file_location(mod_name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - packaging accident
        raise RuntimeError(f"cannot load {path}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[mod_name] = mod
    spec.loader.exec_module(mod)
    return mod


CRC = _load("_ccq_registry_coverage", "check-registry-coverage.py")
PF = _load("_ccq_proof_frontier", "proof-frontier.py")


# ---------------------------------------------------------------------------
# Lean source readers
# ---------------------------------------------------------------------------
def strip_lean_comments(src: str) -> str:
    """Blank out `/- … -/` (nesting) and `--` line comments, preserving offsets.

    ⚠️ Load-bearing. A grep for `^\\s*theorem …_spec` counts declarations that sit
    inside a commented-out block, and this tree has over-counted that way before.
    Newlines are preserved so line-oriented regexes still see the same structure.
    """
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if src.startswith("-/", i) and depth:
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth:
            if src[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


def addr_to_symbol() -> dict[int, str]:
    src = open(GUESTADDRS, encoding="utf-8").read()
    out = {}
    for m in re.finditer(r"def\s+([a-z][a-z0-9_]*)\s*:\s*Nat\s*:=\s*(0x[0-9a-fA-F]+)", src):
        out[int(m.group(2), 16)] = m.group(1)
    return out


TIER_ORDER = (".proven", ".conditional", ".partly")


def row_tiers() -> dict[str, set[str]]:
    """symbol -> the set of proof tiers its `Progress/Routines.lean` rows carry.

    A symbol can hold several rows (per-case, per-arm), so this is a set, and the
    STRONGEST tier is what a composition can lean on.
    """
    src = strip_lean_comments(open(ROUTINES, encoding="utf-8").read())
    out: dict[str, set[str]] = defaultdict(set)
    for sym, tier in re.findall(r'routine\s+"([a-z][a-z0-9_]*)"\s+(\.[a-zA-Z]+)', src):
        out[sym].add(tier)
    # A row whose tier the regex missed still counts as a row; record it untiered
    # rather than dropping the symbol (dropping it would INVENT a blocked row).
    for sym in re.findall(r'routine\s+"([a-z][a-z0-9_]*)"', src):
        out.setdefault(sym, set())
    return out


def best_tier(tiers: set[str]) -> str:
    for t in TIER_ORDER:
        if t in tiers:
            return t
    return "?"


ROW_RE = re.compile(
    r'routine\s+"([a-z][a-z0-9_]*)"\s+\.[a-zA-Z]+\s*(?:\n\s*)?'
    r'\((?:some\s+"([A-Za-z0-9_.]+)"|none)\)'
)


def row_proof_refs() -> dict[str, list[str]]:
    """symbol -> the theorem name each of its rows cites, ONE ENTRY PER ROW.

    ⚠️ A list, not a set, and that is the point: rule 1 below is about a symbol
    having several rows that all cite ONE theorem, which a set would erase.

    A row citing `none` contributes the empty string, so it still counts as a row
    while carrying no contract name.
    """
    src = strip_lean_comments(open(ROUTINES, encoding="utf-8").read())
    out: dict[str, list[str]] = defaultdict(list)
    for sym, thm in ROW_RE.findall(src):
        out[sym].append(thm)
    return out


def weak_contract_rows(refs: dict[str, list[str]],
                       recovered: dict[str, set[str]]) -> dict[str, str]:
    """symbol -> why its registry rows do NOT evidence a whole-routine contract.

    Two proxies, both documented at the top of this file, both sound only in the
    demoting direction:

      RULE 1 (structure) — ≥2 rows, all citing the same theorem.
      RULE 2 (name) — no row cites a whole-routine-suffixed name, and no cited name
                      is one the #12568 namespace rule recovered for this symbol.

    ⛔ NEITHER READS A STATEMENT. The returned string is the reason text rendered in
    the worklist, and it says "proxy" so a reader never mistakes it for a measurement.
    """
    out: dict[str, str] = {}
    for sym, thms in refs.items():
        cited = [t for t in thms if t]
        if len(thms) >= 2 and len(set(thms)) == 1 and cited:
            out[sym] = (f"has {len(thms)} rows all citing `{thms[0]}` — one theorem "
                        "cannot be the whole-routine contract [rule 1, structure]")
            continue
        rec = recovered.get(sym, set())
        if any(CRC.is_whole_routine_spec_name(t) or t in rec for t in cited):
            continue
        shown = ", ".join(f"`{t}`" for t in sorted(set(cited))[:2]) or "no theorem"
        out[sym] = f"cites {shown} — no whole-routine suffix [rule 2, name]"
    return out


def rowed_symbols() -> set[str]:
    """Symbols with a registry row, ANY tier: a `.conditional` row is still a
    callee contract you can compose against, so the question is "is there a row",
    not "is it .proven". The tier is carried separately (`row_tiers`) because it
    decides whether the composed result is unconditional or inherits a gate."""
    return set(row_tiers())


# symbol -> theorem names attributed to it ONLY by the #12568 namespace rule.
# Rebuilt by every `spec_theorems` call. Rule 2 above treats these as whole-routine
# names regardless of suffix: that is the whole finding of #12568 (`pointDouble_spec`
# IS the triple), and the rule carries the address conjunct the plain name lacks —
# the file has to cite `GuestAddrs.<symbol>` for the recovery to fire at all.
NAMESPACE_RECOVERED_NAMES: dict[str, set[str]] = {}


def spec_theorems(symbols: set[str]) -> dict[str, list[tuple[str, str]]]:
    """symbol -> [(theorem, file)] for spec-family theorems, namespace-aware.

    Same suffix table and same #12568 namespace recovery as
    `check-registry-coverage.py` (imported, not restated), plus block-comment
    stripping, which that gate does not do.

    ⚠️ This is a NAME-based map. It answers "a theorem plausibly about this symbol
    exists", NOT "a whole-routine `cpsTripleWithin` at the guest address exists".
    Grading that needs `proof-frontier.py --shape` plus reading the statement, so
    every row this map lights up lands in the needs-read bucket, never in
    startable.
    """
    out: dict[str, list[tuple[str, str]]] = defaultdict(list)
    NAMESPACE_RECOVERED_NAMES.clear()
    for path in sorted(glob.glob(os.path.join(ROOT, "EvmAsm/**/*.lean"), recursive=True)):
        rel = os.path.relpath(path, ROOT)
        if rel.startswith("EvmAsm/Progress/"):
            continue
        try:
            raw = open(path, encoding="utf-8").read()
        except OSError:
            continue
        if "theorem" not in raw:
            continue
        txt = strip_lean_comments(raw)
        for thm in CRC.SPEC_RE.findall(txt):
            sym = CRC.camel_to_snake(CRC.strip_spec_suffix(thm))
            if sym in symbols:
                out[sym].append((thm, rel))
                continue
            recovered = CRC.namespace_attributed(thm, sym, txt, symbols)
            if recovered is not None:
                out[recovered].append((thm, rel))
                NAMESPACE_RECOVERED_NAMES.setdefault(recovered, set()).add(thm)
    return out


def obligation_residuals(symbols: set[str]) -> dict[str, list[int]]:
    """symbol -> [obligation ids] naming it in a `.infra` blocker label.

    `Progress/Obligations.lean` is the machine-readable half of "is this symbol a
    named residual": `.opcode` blockers are EVM mnemonics, `.infra` blockers are
    free text that in practice names routines (`stage_system_call`, `mpt_walk`,
    `witness_codes_index_build`, …). Matching is whole-word over the label text.
    """
    txt = strip_lean_comments(open(OBLIGATIONS, encoding="utf-8").read())
    out: dict[str, list[int]] = defaultdict(list)
    for block in re.split(r"(?m)^\s*\{\s*id\s*:=", txt)[1:]:
        m = re.match(r"\s*(\d+)", block)
        if not m:
            continue
        oid = int(m.group(1))
        labels = " ".join(re.findall(r'\.infra\s+"((?:[^"\\]|\\.)*)"', block, re.S))
        for sym in symbols:
            if re.search(r"(?<![A-Za-z0-9_])" + re.escape(sym) + r"(?![A-Za-z0-9_])", labels):
                if oid not in out[sym]:
                    out[sym].append(oid)
    return out


def issue_residuals(path: str | None, symbols: set[str]) -> dict[str, list[int]] | None:
    """symbol -> [issue numbers] whose title/body names it. `None` when not fetched.

    ⚠️ HEURISTIC, and deliberately reported as such: a symbol appearing in an issue
    body is evidence that someone is talking about it, not proof that it is a NAMED
    RESIDUAL of that issue. Use it to avoid collisions, not to grade work.
    """
    if not path:
        return None
    data = json.load(open(path, encoding="utf-8"))
    out: dict[str, list[int]] = defaultdict(list)
    pats = {s: re.compile(r"(?<![A-Za-z0-9_])" + re.escape(s) + r"(?![A-Za-z0-9_])")
            for s in symbols}
    for item in data:
        hay = (item.get("title") or "") + "\n" + (item.get("body") or "")
        for sym, pat in pats.items():
            if pat.search(hay):
                out[sym].append(int(item["number"]))
    return out


# ---------------------------------------------------------------------------
# shape dump
# ---------------------------------------------------------------------------
DUMP_COLUMNS = 7  # addr, ninstr, backedges, indirect, calls, backcalls, accel


def load(tsv_path: str):
    a2s = addr_to_symbol()
    rows = []
    with open(tsv_path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.rstrip("\n")
            if not line:
                continue
            p = line.split("\t")
            if len(p) != DUMP_COLUMNS:
                raise SystemExit(
                    f"callee-composition-queue: {tsv_path}:{lineno} has {len(p)} columns, "
                    f"expected {DUMP_COLUMNS}.\n"
                    "  This is a pre-#12318 dump, whose back-edge column counts backward "
                    "CALLS as loops\n"
                    "  (114/442 entries misgraded). Rebuild and regenerate:\n"
                    "    lake build EvmAsm.Tests.GuestImageShapeDump\n"
                    "    lake env lean scripts/lean/GuestImageShapeDumpRun.lean > " + tsv_path
                )
            addr = int(p[0])
            calls = [int(x) for x in p[4].split(",")] if p[4] else []
            rows.append({
                "addr": addr,
                "symbol": a2s.get(addr, f"?{addr:x}"),
                "ninstr": int(p[1]),
                "backedges": int(p[2]),
                "indirect": p[3] == "1",
                "callees": [a2s.get(c, f"?{c:x}") for c in calls],
                "backcalls": int(p[5]),
                "accel": p[6] == "1",
            })
    return rows


def classify(rows, rowed, specs, tiers=None, weak=None):
    """Annotate each row and assign it a bucket.

    Buckets, and why there are three rather than two:

      startable  — loop-free, unrowed, EVERY callee carries a registry row, and no
                   callee's rows trip a weak-contract proxy.
      needs-read — loop-free, unrowed, and everything blocking confidence is a
                   READ rather than missing work. Two ways in:
                     (a) a callee has a spec-family theorem but no registry row. A
                         theorem is not a row: it may be a fragment, a model-only
                         statement, or anchored at a free `base`.
                     (b) a callee HAS rows, but they trip rule 1 or rule 2 above —
                         N rows citing one theorem, or no whole-routine-suffixed
                         name among them. A row is not a contract.
                   Either way the remedy is the same: `proof-frontier.py --shape`
                   plus reading the statement.
      blocked    — some callee has neither row nor theorem. Those are the demand
                   queue.

    ⛔ The split exists because mislabelling a blocked row as startable costs a
    collaborator a day, and this tool cannot read a theorem statement.

    ⚠️ `weak` demotes only; nothing here can move a row INTO `startable`. A
    name/structure proxy is sound in that one direction and in no other.

    Orthogonally, `gated_callees` names the callees whose strongest row is NOT
    `.proven`. Those rows compose fine, but the result inherits their gate — the
    composed contract is `.conditional`/`.partly` too, not `.proven`. Nothing here
    is blocked by that; it changes what the finished row may claim.
    """
    tiers = tiers if tiers is not None else {}
    weak = weak if weak is not None else {}
    by_sym = {}
    for r in rows:
        uniq = []
        for c in r["callees"]:
            if c not in uniq:
                uniq.append(c)
        r["uniq_callees"] = uniq
        by_sym[r["symbol"]] = r

    # In-degree over the IMAGE call graph (Program-level, exact for linked code).
    indeg_image: dict[str, int] = defaultdict(int)
    for r in rows:
        for c in r["uniq_callees"]:
            indeg_image[c] += 1
    # In-degree over the FIXTURE call graph (broader: includes callers not linked).
    indeg_fix: dict[str, int] = defaultdict(int)
    for _caller, callees in PF.fixture_edges().items():
        for c in callees:
            indeg_fix[c] += 1

    for r in rows:
        r["loopfree"] = r["backedges"] == 0 and not r["indirect"]
        r["rowed"] = r["symbol"] in rowed
        r["self_specs"] = specs.get(r["symbol"], [])
        r["indeg_image"] = indeg_image.get(r["symbol"], 0)
        r["indeg_fixture"] = indeg_fix.get(r["symbol"], 0)
        r["missing"] = [c for c in r["uniq_callees"] if c not in rowed]
        r["missing_hard"] = [c for c in r["missing"] if not specs.get(c)]
        r["missing_soft"] = [c for c in r["missing"] if specs.get(c)]
        r["gated_callees"] = [(c, best_tier(tiers[c])) for c in r["uniq_callees"]
                              if c in tiers and best_tier(tiers[c]) != ".proven"]
        r["weak_callees"] = [(c, weak[c]) for c in r["uniq_callees"] if c in weak]
        if r["rowed"] or not r["loopfree"]:
            r["bucket"] = "n/a"
        elif not r["missing"] and not r["weak_callees"]:
            r["bucket"] = "startable"
        elif not r["missing_hard"]:
            r["bucket"] = "needs-read"
        else:
            r["bucket"] = "blocked"
        r["startable"] = r["bucket"] == "startable"
    return rows


# ---------------------------------------------------------------------------
# the #12318 lane
# ---------------------------------------------------------------------------
def lane(rows):
    """The population #12318 is about: in-image, unrowed, loop-free, WITH calls."""
    return [r for r in rows if r["loopfree"] and not r["rowed"] and r["uniq_callees"]]


def sort_key(r):
    order = {"startable": 0, "needs-read": 1, "blocked": 2}
    return (order.get(r["bucket"], 3), -r["indeg_image"], -r["indeg_fixture"],
            r["ninstr"], r["symbol"])


def residual_cell(sym, obl, iss):
    bits = []
    if obl.get(sym):
        bits.append("obl " + ",".join(f"#{i}" for i in sorted(obl[sym])))
    if iss is None:
        bits.append("issues ?")
    elif iss.get(sym):
        shown = sorted(iss[sym])[:4]
        bits.append("gh " + ",".join(f"#{i}" for i in shown)
                    + ("+" if len(iss[sym]) > len(shown) else ""))
    return "; ".join(bits) if bits else "—"


def census(rows, rowed):
    inimg = len(rows)
    unrowed = [r for r in rows if not r["rowed"]]
    lf = [r for r in rows if r["loopfree"]]
    lane_rows = lane(rows)
    return {
        "entries": inimg,
        "rowed_total": len(rowed),
        "rowed_in_image": inimg - len(unrowed),
        "unrowed": len(unrowed),
        "loopfree": len(lf),
        "loopbearing": inimg - len(lf),
        "lane": len(lane_rows),
        "lane_startable": sum(1 for r in lane_rows if r["bucket"] == "startable"),
        "lane_needsread": sum(1 for r in lane_rows if r["bucket"] == "needs-read"),
        "lane_blocked": sum(1 for r in lane_rows if r["bucket"] == "blocked"),
        "lane_startable_unconditional": sum(
            1 for r in lane_rows if r["bucket"] == "startable" and not r["gated_callees"]),
        "lane_weak": sum(1 for r in lane_rows
                         if r["bucket"] == "needs-read" and r["weak_callees"]),
        "lane_accel": sum(1 for r in lane_rows if r["accel"]),
        "callfree_unrowed": sum(1 for r in rows
                                if r["loopfree"] and not r["rowed"] and not r["uniq_callees"]),
    }


def print_worklist(rows, rowed, obl, iss):
    c = census(rows, rowed)
    lane_rows = sorted(lane(rows), key=sort_key)
    blockers: dict[str, int] = defaultdict(int)
    for r in lane_rows:
        for m in r["missing"]:
            blockers[m] += 1

    print("## The population: **{lane}**, not 251 — and the 251 was a shape-parser artefact"
          .format(**c))
    print()
    print("| class (in-image, from the `Program`s) | count |")
    print("|---|---:|")
    print(f"| `guestImageEntries` | {c['entries']} |")
    print(f"| …rowed in `Progress/Routines.lean` | {c['rowed_in_image']} |")
    print(f"| …unrowed | {c['unrowed']} |")
    print(f"| loop-free (no in-extent back-edge, no indirect jump) | {c['loopfree']} |")
    print(f"| loop-bearing | {c['loopbearing']} |")
    print(f"| **unrowed + loop-free + WITH calls — this lane** | **{c['lane']}** |")
    print(f"| unrowed + loop-free + call-free | {c['callfree_unrowed']} |")
    print()
    print(f"Of the {c['lane']}: **{c['lane_startable']} startable today**, "
          f"{c['lane_needsread']} needs-read, {c['lane_blocked']} blocked. "
          f"{c['lane_accel']} of them issue a ZisK accelerator `CSRS` (different recipe).")
    print()
    print(f"⚠️ Of the {c['lane_startable']} startable, "
          f"**{c['lane_startable_unconditional']} have every callee at `.proven`**; the rest "
          "compose against a `.conditional`/`.partly` callee row and so INHERIT its gate — "
          "the composed row is `.conditional`, not `.proven`. That is not a blocker, but a "
          "row that claims otherwise overclaims. The `gate inherited from` note names the "
          "callee and its tier.")
    print()
    print(f"⚠️ **{c['lane_weak']} rows that a row-count test would call startable are in "
          "`needs-read` instead**, because a rowed callee's rows do not evidence a "
          "whole-routine contract. Two proxies, **both name/structure, neither a statement "
          "read**: (1) the callee symbol has **≥2 rows all citing one theorem** — the "
          "`header_extended_decode` shape, five `.proven` rows and one per-field u64 "
          "segment lemma between them; (2) **no row cites a theorem whose name carries a "
          "whole-routine suffix** (`_spec_within` / `Flat_spec`, plus the #12568 "
          "namespace-recovered forms — `pointDouble_spec` IS "
          "`secp256k1_point_double`'s triple, so it is not demoted). The suffix table is "
          "imported from `check-registry-coverage.py`'s tier-A split, not restated. "
          "⛔ These only ever move a row OUT of the confident bucket — a demotion on a "
          "proxy is safe, a promotion would not be, and none is offered. Rule 2 also "
          "fires on pre-convention names (`u256Eq_spec`, `frameBase_spec`) that are "
          "probably genuine whole-routine triples; the proxy cannot tell, which is "
          "exactly what `needs-read` means.")
    print()
    print("### How to claim a row")
    print()
    print("Edit this comment and rewrite your row's symbol cell as")
    print("~~``some_routine``~~ **@you** — strike it through and append your handle.")
    print("Unstrike it if you drop the row. One row per PR; rows are independent")
    print("(triple + registry row), so there is no merge order between them.")
    print()
    print("| claim | symbol | instrs | in-deg (image / fixtures) | callees | "
          "named residual | note |")
    print("|---|---|---:|---:|---|---|---|")
    for r in lane_rows:
        if r["bucket"] == "startable":
            note = "✅ every callee rowed"
        elif r["bucket"] == "needs-read":
            bits = []
            if r["missing_soft"]:
                bits.append(", ".join(f"`{m}`" for m in r["missing_soft"])
                            + " has a theorem but no row")
            bits += [f"`{cal}` {why}" for cal, why in r["weak_callees"]]
            note = "⚠️ read first: " + "; ".join(bits)
            if r["weak_callees"]:
                note += " — ⛔ a PROXY grade, not a statement read"
        else:
            note = "⛔ blocked on " + ", ".join(f"`{m}`" for m in r["missing_hard"])
            if r["weak_callees"]:
                note += " · also weak-contract: " + ", ".join(
                    f"`{cal}`" for cal, _ in r["weak_callees"])
        if r["gated_callees"]:
            note += " · gate inherited from " + ", ".join(
                f"`{c}` ({t})" for c, t in r["gated_callees"])
        if r["accel"]:
            note += " · ⚡ `CSRS`"
        if r["self_specs"]:
            note += " · has `%s`" % r["self_specs"][0][0]
        print(f"| | `{r['symbol']}` | {r['ninstr']} | "
              f"{r['indeg_image']} / {r['indeg_fixture']} | "
              + ", ".join(f"`{c}`" for c in r["uniq_callees"]) + " | "
              + residual_cell(r["symbol"], obl, iss) + f" | {note} |")
    if blockers:
        print()
        print("### Demand queue — unrowed callees, ranked by how many lane rows they block")
        print()
        print("| callee | blocks | in-deg (image / fixtures) | state |")
        print("|---|---:|---:|---|")
        by_sym = {r["symbol"]: r for r in rows}
        for sym, n in sorted(blockers.items(), key=lambda kv: (-kv[1], kv[0])):
            b = by_sym.get(sym)
            shape = "⚠️ linked address, no `guestImageEntries` pairing — transcribe first"
            if b is not None:
                shape = ("loop-free" if b["loopfree"] else "loop-bearing")
                shape += f", {b['ninstr']} instrs"
                if b["accel"]:
                    shape += ", `CSRS`"
            print(f"| `{sym}` | {n} | "
                  f"{b['indeg_image'] if b else 0} / {b['indeg_fixture'] if b else 0} | "
                  f"{shape} |")


def print_text(rows, rowed, obl, iss, limit):
    c = census(rows, rowed)
    lane_rows = sorted(lane(rows), key=sort_key)
    callfree = [r for r in rows if r["loopfree"] and not r["rowed"] and not r["uniq_callees"]]
    print(f"callee-composition-queue: {c['entries']} image entries, "
          f"{c['rowed_total']} rowed symbols")
    print(f"  loop-free, no indirect                 : {c['loopfree']}")
    print(f"    call-free AND unrowed                : {c['callfree_unrowed']}")
    print(f"    with calls AND unrowed (#12318 lane) : {c['lane']}")
    print(f"      startable / needs-read / blocked   : "
          f"{c['lane_startable']} / {c['lane_needsread']} / {c['lane_blocked']}")
    print(f"        of needs-read, demoted by a weak-contract PROXY : {c['lane_weak']}")
    print(f"  loop-bearing                           : {c['loopbearing']}")
    print()
    print("STARTABLE NOW — call-free, loop-free, unrowed (smallest first):")
    for r in sorted(callfree, key=lambda r: r["ninstr"])[:limit]:
        print(f"  {r['symbol']:<48} {r['ninstr']:>4} instrs")
    print()
    print("#12318 LANE — loop-free WITH calls, unrowed (startable first, in-degree desc):")
    for r in lane_rows:
        print(f"  {r['symbol']:<48} {r['ninstr']:>4} instrs  in-deg {r['indeg_image']:>2}"
              f"/{r['indeg_fixture']:<2}  {r['bucket']:<10} "
              f"{residual_cell(r['symbol'], obl, iss)}"
              + ("" if r["bucket"] == "startable"
                 else "  <- " + ",".join(r["missing"])))
    blockers: dict[str, int] = defaultdict(int)
    for r in lane_rows:
        for m in r["missing"]:
            blockers[m] += 1
    if blockers:
        print()
        print("Unrowed callees blocking the lane (row these first, #12035):")
        for sym, n in sorted(blockers.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {sym:<48} blocks {n}")


# ---------------------------------------------------------------------------
# self-test
# ---------------------------------------------------------------------------
_BRANCH = re.compile(r"^(beq|bne|blt|bge|bltu|bgeu|beqz|bnez|bltz|bgez|blez|bgtz|j|jal)"
                     r"\b\s*(.*)$")


def asm_backedges(txt: str) -> int:
    """Back-edge count re-derived from ASSEMBLY TEXT, independently of the dump.

    Deliberately a different algorithm on a different input: labels resolved by
    position (plus the `emitProgram` numeric `.-N` form), semicolon-packed lines
    split, `#` comments dropped. It exists to falsify the `Program`-level grade,
    so it must not share code with it.
    """
    units: list[str] = []
    for raw in txt.splitlines():
        for part in raw.split("#")[0].split(";"):
            s = part.strip()
            if s:
                units.append(s)
    labels: dict[str, int] = {}
    for i, u in enumerate(units):
        m = re.match(r"^([.\w$]+):", u)
        if m:
            labels.setdefault(m.group(1), i)
    n = 0
    for i, u in enumerate(units):
        m = _BRANCH.match(re.sub(r"^[.\w$]+:\s*", "", u))
        if not m:
            continue
        tgt = m.group(2).split(",")[-1].strip() if m.group(2) else ""
        if tgt.startswith(".-") or (tgt in labels and labels[tgt] < i):
            n += 1
    return n


def fixture_texts() -> dict[str, str]:
    out = {}
    for f in sorted(glob.glob(os.path.join(FIXTURES, "*.s"))):
        txt = open(f, encoding="utf-8").read()
        head = txt.strip().splitlines()[0].strip() if txt.strip() else ""
        if head.endswith(":"):
            out[head[:-1]] = txt
    return out


def self_test(tsv_path: str) -> int:
    ok = True

    def check(label, cond, detail=""):
        nonlocal ok
        print(f"  {'PASS' if cond else 'FAIL'}  {label}" + (f" — {detail}" if detail else ""))
        if not cond:
            ok = False

    tiers = row_tiers()
    rowed = set(tiers)
    raw = load(tsv_path)
    symbols = set(addr_to_symbol().values())
    specs = spec_theorems(symbols)
    refs = row_proof_refs()
    weak = weak_contract_rows(refs, NAMESPACE_RECOVERED_NAMES)
    rows = classify(raw, rowed, specs, tiers, weak)
    c = census(rows, rowed)
    lane_rows = lane(rows)

    # ⚠️ NON-VACUITY FIRST. An earlier version of this self-test passed all five of
    # its checks while measuring ZERO routines — every `all(...)` over an empty list
    # is true, so a broken input made the suite green. Population floors come before
    # any invariant.
    check("population is non-empty (guards against a vacuous pass)",
          len(rows) > 100, f"{len(rows)} image entries")
    check("some routine is loop-free", c["loopfree"] > 0, f"{c['loopfree']}")
    check("the #12318 lane is non-empty", c["lane"] > 0, f"{c['lane']}")
    check("some lane row is startable", c["lane_startable"] > 0, f"{c['lane_startable']}")

    # Controls with independently-known answers: proved by hand, so their shapes are
    # known without this tool. Counts must equal the `#guard <sym>_prog.length` in
    # their source files.
    known = {
        "call_frame_set_calldata": (4, 0),   # 3-instruction body + ret, no loop
        "u256_from_u64_be":       (19, 0),   # 18 + ret, loop-free
        "secf_eq32":              (15, 1),   # 14 + ret, byte-scan loop
        "blsg_eq48":              (15, 1),   # same shape at 48 bytes
    }
    bysym = {r["symbol"]: r for r in rows}
    for sym, (n, back) in known.items():
        r = bysym.get(sym)
        check(f"control {sym}: {n} instrs, {back} back-edge(s)",
              r is not None and r["ninstr"] == n and r["backedges"] == back,
              "" if r is None else f"got {r['ninstr']} instrs, {r['backedges']} back-edges")

    # ⭐ The check that caught the defect this tool shipped with (#12318): a `j` to a
    # lower-addressed callee is a CALL, not a loop. `mpt_delete_walk_db`'s entire
    # body is that one instruction, and the pre-fix dump graded it loop-bearing.
    r = bysym.get("mpt_delete_walk_db")
    check("negative-offset CALL is not a back-edge (mpt_delete_walk_db, 1 instr)",
          r is not None and r["ninstr"] == 1 and r["backedges"] == 0 and r["backcalls"] == 1,
          "" if r is None else f"n={r['ninstr']} back={r['backedges']} "
                               f"backcalls={r['backcalls']}")

    # ⭐ FALSIFICATION BY AN INDEPENDENT MEASUREMENT. Re-derive the loop grade from
    # the fixture ASSEMBLY TEXT and require agreement everywhere. Pre-fix this stood
    # at 327/441; a regression that reintroduces the backward-call confusion cannot
    # pass it.
    fx = fixture_texts()
    agree = disagree = 0
    examples = []
    for r in rows:
        txt = fx.get(r["symbol"])
        if txt is None:
            continue
        if (asm_backedges(txt) > 0) == (r["backedges"] > 0):
            agree += 1
        else:
            disagree += 1
            if len(examples) < 5:
                examples.append(r["symbol"])
    check("fixture-bearing population is large (non-vacuous cross-check)",
          agree + disagree > 300, f"{agree + disagree} entries carry a fixture")
    check("Program-level loop grade agrees with the independent asm-text grade",
          disagree == 0, f"{agree} agree, {disagree} disagree {examples}")

    # ⭐ PLANTED WRONG INPUT 1: a stale (pre-#12318, 5-column) dump must be REFUSED,
    # not read. Reading it silently reproduces the 114-entry misgrade.
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".tsv", delete=False) as fh:
        fh.write("2147489984\t121\t3\t0\t\n")
        stale = fh.name
    try:
        load(stale)
        caught = False
    except SystemExit:
        caught = True
    finally:
        os.unlink(stale)
    check("planted stale 5-column dump is refused", caught)

    # ⭐ PLANTED WRONG INPUT 2: a routine whose callee has NO row must never be
    # graded startable. Plant an unrowed callee on a startable row and require the
    # bucket to move.
    victim = next((r for r in lane_rows if r["bucket"] == "startable"), None)
    if victim is None:
        check("planted unrowed callee demotes a startable row", False, "no startable row")
    else:
        planted = [dict(victim)]
        planted[0]["callees"] = victim["callees"] + ["definitely_not_a_rowed_symbol"]
        planted = classify(planted, rowed, specs, tiers, weak)
        check("planted unrowed callee demotes a startable row",
              planted[0]["bucket"] == "blocked",
              f"{victim['symbol']} -> {planted[0]['bucket']}")

    # ⭐ PLANTED WRONG INPUT 3: a commented-out theorem must not count as a spec.
    planted_src = "/-\ntheorem ghost_symbol_spec : True := trivial\n-/\n"
    check("theorem inside a block comment is not counted",
          "theorem" not in strip_lean_comments(planted_src),
          repr(strip_lean_comments(planted_src).strip()))
    check("theorem outside a block comment IS counted",
          "theorem" in strip_lean_comments("theorem real_spec : True := trivial\n"))

    # ⭐ The #12568 namespace rule must be live, not merely imported: if it recovered
    # nothing, the reuse is decorative and the blind spot is back.
    check("namespace recovery is reachable (#12568 rule imported, not restated)",
          CRC.namespace_attributed("pointDouble_spec", "point_double",
                                   "GuestAddrs.secp256k1_point_double", symbols)
          == "secp256k1_point_double")

    # ⭐ PLANTED WRONG INPUT 4: a callee whose strongest row is `.conditional` must
    # show up as a gate the composed row inherits, never as a clean `.proven`
    # composition. `rlp_item_span` is `.conditional` in the registry today.
    gate_probe = classify([dict(victim, callees=["rlp_item_span", "mset_memcpy"])]
                          if victim else [], rowed, specs, tiers, weak)
    check("a `.conditional` callee is reported as an inherited gate",
          bool(gate_probe) and gate_probe[0]["gated_callees"] == [("rlp_item_span",
                                                                   ".conditional")],
          "" if not gate_probe else str(gate_probe[0]["gated_callees"]))
    check("tier reading is non-vacuous (both gated and ungated startable rows exist)",
          c["lane_startable_unconditional"] > 0
          and c["lane_startable_unconditional"] < c["lane_startable"],
          f"{c['lane_startable_unconditional']} of {c['lane_startable']} ungated")

    # ⭐ PLANTED WRONG INPUT 5 — RULE 1 (structure proxy). A SYNTHETIC symbol with two
    # rows citing one theorem must be graded weak, and a caller of it must not be
    # startable. Planted rather than read off the tree so the check keeps working the
    # day `header_extended_decode` gains a whole-routine triple. The negative control
    # sits alongside it: two rows citing DIFFERENT theorems must NOT trip rule 1.
    plant_rule1 = weak_contract_rows(
        {"planted_two_rows_one_thm": ["planted_seg_spec_within", "planted_seg_spec_within"],
         "planted_two_rows_two_thms": ["planted_a_spec_within", "planted_b_spec_within"]},
        {})
    check("RULE 1: 2 rows citing ONE theorem is graded a weak contract",
          "planted_two_rows_one_thm" in plant_rule1,
          plant_rule1.get("planted_two_rows_one_thm", "not caught"))
    check("RULE 1 control: 2 rows citing DIFFERENT whole-routine theorems is not weak",
          "planted_two_rows_two_thms" not in plant_rule1,
          plant_rule1.get("planted_two_rows_two_thms", ""))
    r1 = classify([dict(victim, callees=["planted_two_rows_one_thm"])] if victim else [],
                  rowed | {"planted_two_rows_one_thm"}, specs, tiers, plant_rule1)
    check("RULE 1: a caller of that symbol is demoted startable -> needs-read",
          bool(r1) and r1[0]["bucket"] == "needs-read" and r1[0]["weak_callees"],
          "" if not r1 else r1[0]["bucket"])

    # ⭐ PLANTED WRONG INPUT 6 — RULE 2 (name proxy). A single row citing a name with no
    # whole-routine suffix must be graded weak; the same name WITH the suffix must not.
    # ⚠️ Third case is the #12568 inheritance, and it is the one that would silently
    # re-break: `pointDouble_spec` carries no whole-routine suffix, but the namespace
    # rule recovered it FOR that symbol (with a `GuestAddrs.<sym>` citation), so it must
    # survive. If this ever fails, the recovery has been dropped, not tightened.
    plant_rule2 = weak_contract_rows(
        {"planted_bare_spec": ["plantedThing_spec"],
         "planted_within_spec": ["planted_within_spec_within"],
         "planted_flat_spec": ["plantedThingFlat_spec"],
         "planted_domain_arm": ["planted_arm_spec_within_empty_section"],
         "planted_ns_recovered": ["plantedNs_spec"]},
        {"planted_ns_recovered": {"plantedNs_spec"}})
    check("RULE 2: a row citing a name with no whole-routine suffix is weak",
          "planted_bare_spec" in plant_rule2,
          plant_rule2.get("planted_bare_spec", "not caught"))
    check("RULE 2 control: `_spec_within` and `Flat_spec` names are not weak",
          "planted_within_spec" not in plant_rule2
          and "planted_flat_spec" not in plant_rule2)
    check("RULE 2: a domain-restricted arm (`_spec_within_empty_section`) is weak",
          "planted_domain_arm" in plant_rule2,
          plant_rule2.get("planted_domain_arm", "not caught"))
    check("RULE 2 inherits #12568: a namespace-recovered name is NOT demoted",
          "planted_ns_recovered" not in plant_rule2,
          plant_rule2.get("planted_ns_recovered", ""))
    r2 = classify([dict(victim, callees=["planted_bare_spec"])] if victim else [],
                  rowed | {"planted_bare_spec"}, specs, tiers, plant_rule2)
    check("RULE 2: a caller of that symbol is demoted startable -> needs-read",
          bool(r2) and r2[0]["bucket"] == "needs-read" and r2[0]["weak_callees"],
          "" if not r2 else r2[0]["bucket"])

    # ⚠️ NON-VACUITY for the two rules on the REAL tree. Planted cases prove the
    # predicate works; these prove it is wired to live data and is not grading
    # everything (a rule that fires on every symbol carries no information).
    check("the registry row reader sees every row (no silently dropped `routine` line)",
          sum(len(v) for v in refs.values())
          == len(re.findall(r'routine\s+"[a-z][a-z0-9_]*"',
                            strip_lean_comments(open(ROUTINES, encoding="utf-8").read()))),
          f"{sum(len(v) for v in refs.values())} rows parsed")
    check("weak-contract grading is non-vacuous and not universal",
          0 < len(weak) < len(refs), f"{len(weak)} of {len(refs)} rowed symbols")
    check("`header_extended_decode` is graded weak by RULE 1 on the live registry",
          "header_extended_decode" in weak
          and "rows all citing" in weak["header_extended_decode"],
          weak.get("header_extended_decode", "NOT CAUGHT — the #12799 counterexample "
                                             "no longer trips rule 1"))
    check("the proxies actually moved rows out of startable",
          c["lane_weak"] > 0, f"{c['lane_weak']} demoted to needs-read")

    # Bucket invariants.
    check("startable implies no callee trips a weak-contract proxy",
          all(not r["weak_callees"] for r in rows if r["startable"]))
    check("startable implies loop-free and unrowed",
          all(r["loopfree"] and not r["rowed"] for r in rows if r["startable"]))
    check("startable implies every callee rowed",
          all(all(c in rowed for c in r["uniq_callees"])
              for r in rows if r["startable"]))
    check("needs-read rows have a read to do (theorem-only OR weak-contract callee) "
          "and no row-less one",
          all((r["missing_soft"] or r["weak_callees"]) and not r["missing_hard"]
              for r in rows if r["bucket"] == "needs-read"))
    check("in-degree is consistent with the edge list",
          all(r["indeg_image"] == sum(1 for q in rows if r["symbol"] in q["uniq_callees"])
              for r in rows))
    print()
    print(f"  measured: {c['entries']} entries | {c['loopfree']} loop-free | "
          f"{c['callfree_unrowed']} call-free unrowed | {c['lane']} in the #12318 lane "
          f"({c['lane_startable']} startable, {c['lane_needsread']} needs-read of which "
          f"{c['lane_weak']} demoted by a weak-contract proxy)")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tsv", default="/tmp/shape.tsv",
                    help="shape dump from scripts/lean/GuestImageShapeDumpRun.lean")
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--worklist", action="store_true",
                    help="emit the #12318 claimable worklist as markdown")
    ap.add_argument("--issues-json", default=None,
                    help="gh issue list --json number,title,body dump; without it the "
                         "open-issue column reads '?', never 'no'")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--limit", type=int, default=40)
    args = ap.parse_args()

    if not os.path.isfile(args.tsv):
        print(f"callee-composition-queue: no shape dump at {args.tsv}", file=sys.stderr)
        print("  regenerate with:", file=sys.stderr)
        print("    lake build EvmAsm.Tests.GuestImageShapeDump", file=sys.stderr)
        print("    lake env lean scripts/lean/GuestImageShapeDumpRun.lean > "
              f"{args.tsv}", file=sys.stderr)
        return 2

    if args.self_test:
        return self_test(args.tsv)

    tiers = row_tiers()
    rowed = set(tiers)
    symbols = set(addr_to_symbol().values())
    specs = spec_theorems(symbols)
    weak = weak_contract_rows(row_proof_refs(), NAMESPACE_RECOVERED_NAMES)
    rows = classify(load(args.tsv), rowed, specs, tiers, weak)
    obl = obligation_residuals(symbols)
    iss = issue_residuals(args.issues_json, symbols)

    if args.worklist:
        print_worklist(rows, rowed, obl, iss)
        return 0

    if args.markdown:
        c = census(rows, rowed)
        print("| class | count |")
        print("|---|---|")
        print(f"| image entries | {c['entries']} |")
        print(f"| loop-free, no indirect | {c['loopfree']} |")
        print(f"| ...call-free **and unrowed** | {c['callfree_unrowed']} |")
        print(f"| ...with calls **and unrowed** (#12318 lane) | **{c['lane']}** |")
        print(f"| loop-bearing | {c['loopbearing']} |")
        print()
        for r in sorted(lane(rows), key=sort_key):
            print(f"| `{r['symbol']}` | {r['ninstr']} | {r['bucket']} |")
        return 0

    print_text(rows, rowed, obl, iss, args.limit)
    return 0


if __name__ == "__main__":
    sys.exit(main())
