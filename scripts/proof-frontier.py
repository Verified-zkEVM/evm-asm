#!/usr/bin/env python3
"""proof-frontier.py -- the startable proof frontier, computed not hand-annotated.

Mechanizes the census that docs/leaf-routine-targets.md (GH #11312) specifies but
hand-executes. Three hand annotations drifted and mis-aimed proof issues:

  1. derive_withdrawal_requests / derive_consolidation_requests were annotated as
     leaves though they are 7-instruction stubs that tail-jump into
     stage_system_call and thence the whole interpreter (#11578).
  2. a runners-up bullet claimed the field towers had no assertion vocabulary and
     named the wrong prime (#11676).
  3. #11575 was filed as "eight mechanical forks missing" when all eight siblings
     already had sorry-free triples (this script's present-but-unrowed state is
     exactly the class that filing missed).

The census:

  universe          = fixture symbols (each scripts/asm-fixtures/*.s first line
                      is `symbol:`) union rowed symbols
                      (Progress/Routines.lean) union correspondence symbols.
  callee edges      = per fixture, the `jal ra, <sym>` targets plus tail-calls
                      (bare `j <sym>`, including the spaces-before-comment form
                      -- see callees_of; a broken tail-call regex silently
                      reproduces error 1 above).
  witnessed(sym)    = some `routine "<sym>"` row carries a proofRef.
  startable(sym)    = every symbol in sym's transitive closure is witnessed.
                      (TRUE for a genuine leaf: empty closure, `all` over empty.)
  frontier          = startable symbols that are not already rowed.

Three states per symbol -- NEVER collapsed (see below):

  absent                : no `*_spec`-family theorem anywhere in EvmAsm/.
  present-but-unrowed   : a theorem exists (matching one of the naming
                          conventions, see SPEC_SUFFIXES) but no Routines.lean
                          row.  THE actionable class: the #11637 row-existence
                          debt.  This is also the state #11575's siblings were
                          in at filing time -- a census that reads only
                          Routines.lean (or only AxiomWitnesses.lean, which is
                          GENERATED from the rows) classifies them UNPROVEN and
                          reproduces the error it exists to prevent.
  rowed                 : a Routines.lean row exists.

Theorem presence is therefore read from EvmAsm/ sources (spec_bearing_syms),
never from the registry and never from AxiomWitnesses -- those are downstream.

Gate: advisory like scripts/check-obligation-blockers.sh. exit 0 by default;
--strict fails if the current doc table claims startable for a symbol the census
says is not (and prints the disagreement, it does not edit the doc).

Usage:
  scripts/proof-frontier.py            # census + frontier queue, exit 0
  scripts/proof-frontier.py --strict   # also fail on doc/census disagreement
  scripts/proof-frontier.py --self-test  # only run the classifier self-test
"""

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FIXTURES = REPO / "scripts/asm-fixtures"
MANIFEST = FIXTURES / "MANIFEST.tsv"
GUEST_ADDRS = REPO / "EvmAsm/Codegen/GuestAddrs.lean"
ROUTINES = REPO / "EvmAsm/Progress/Routines.lean"
CORR = REPO / "EvmAsm/Progress/Correspondence.lean"
DOC = REPO / "docs/leaf-routine-targets.md"


# -- theorem naming conventions (enumerated for the self-test) -----------------
# Order matters for suffix stripping: _fnspec first because there 'spec' is
# preceded by 'n' not '_' (the #11042/#11903 lesson). Mirrors
# check-registry-coverage's SPEC_SUFFIXES exactly.
SPEC_SUFFIXES = ("_fnspec", "Fn_spec", "Flat_spec", "_spec_within", "_spec")
_SPEC_ALT = "|".join(re.escape(s) for s in SPEC_SUFFIXES)
SPEC_RE = re.compile(r"^\s*theorem\s+(\w*(?:" + _SPEC_ALT + r"))\b", re.M)


# -- call-graph edges ----------------------------------------------------------
# Two regexes, NOT the check_routine_liveness `[;"']\s*j` family: a tail-call is
#   j stage_system_call          # tail call: ...
# with SPACES before the comment.  Anchored line-start + word boundary is the
# only form that sees it; anything requiring '#' immediately after the target
# reports derive_* as leaves (the #11578 mis-annotation) and stage_system_call's
# whole subtree as unexplored.
JAL_RE = re.compile(r"\bjal\s+(?:ra|x1|x5|t0),\s*([A-Za-z_][A-Za-z0-9_]*)")
TAIL_RE = re.compile(r"^\s*j\s+([A-Za-z_][A-Za-z0-9_]*)\b", re.M)


# -- registry / source readers --------------------------------------------------
ROW_RE = re.compile(r'^  routine "([A-Za-z0-9_]+)"', re.M)
REF_RE = re.compile(r'\(some\s+"([^"]+)"\)')
CORR_RE = re.compile(r'routine\s+:=\s*"([A-Za-z0-9_]+)"')
GUEST_ADDRS_RE = re.compile(r"^def ([a-z_0-9]+) : Nat := 0x", re.M)


def camel_to_snake(name):
    first = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name)
    second = re.sub(r"([A-Z])([A-Z][a-z])", r"\1_\2", first)
    return second.lower().strip("_")


def style_snake_of_theorem(thm):
    """Recover the guest symbol from a spec theorem name by stripping the
    naming-convention suffix, else None. Multi-row symbols like rlp_walk_next
    use account-specialised names (account_rlp_walk_next_field0_spec_within);
    strip the suffix, do NOT prefix-match a census symbol."""
    for suffix in SPEC_SUFFIXES:
        if thm.endswith(suffix):
            return camel_to_snake(thm[: -len(suffix)])
    return None


def parse_routines(text):
    """(symbol, tier, proofref-or-None) rows.  Rows span lines: `(some "ref")`
    can sit on a continuation line, so split on the 2-space `routine "` anchor
    and search each block rather than parsing line-by-line."""
    rows = []
    for block in re.split(r"(?m)^  routine \"", text)[1:]:
        m = re.match(r'([A-Za-z0-9_]+)"\s+\.(\w+)', block)
        if not m:
            continue
        sym, tier = m.group(1), m.group(2)
        ref = REF_RE.search(block)
        rows.append((sym, tier, ref.group(1) if ref else None))
    return rows


def rowed_symbols(rows):
    return {sym for sym, _tier, _ref in rows}


def witnessed_symbols(rows):
    return {sym for sym, _tier, ref in rows if ref}


def correspondence_symbols(text):
    return set(CORR_RE.findall(text))


def linked_symbols(text):
    return set(GUEST_ADDRS_RE.findall(text))


def spec_bearing_syms():
    """symbol -> set of (relative file, theorem) for spec theorems in EvmAsm/
    sources (excluding the Progress/ registry dir itself).  This is the
    'present' signal for the three-state classifier -- NOT the registry, NOT
    AxiomWitnesses (both are downstream of the rows)."""
    found = {}
    for path in sorted(REPO.glob("EvmAsm/**/*.lean")):
        if "EvmAsm/Progress/" in str(path):
            continue
        txt = path.read_text(errors="replace")
        if "theorem" not in txt:
            continue
        rel = path.relative_to(REPO)
        for m in SPEC_RE.finditer(txt):
            sym = style_snake_of_theorem(m.group(1))
            if sym:
                found.setdefault(sym, set()).add((str(rel), m.group(1)))
    return found


# -- fixtures / call graph -------------------------------------------------------
def manifest_symbols():
    syms = set()
    for line in MANIFEST.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 1:
            continue
        fixture = FIXTURES / (fields[0] + ".s")
        if fixture.exists():
            first = fixture.read_text(errors="replace").splitlines()[0].strip()
            if first.endswith(":"):
                first = first[:-1]
            if first:
                syms.add(first)
    return syms


def callees_of(fixture_text):
    return set(JAL_RE.findall(fixture_text)) | set(TAIL_RE.findall(fixture_text))


def fixture_edges():
    """symbol -> set of callee symbols, from the emitted fixtures."""
    edges = {}
    for line in MANIFEST.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 1:
            continue
        fixture = FIXTURES / (fields[0] + ".s")
        if not fixture.exists():
            continue
        txt = fixture.read_text(errors="replace")
        lines = txt.splitlines()
        if not lines:
            continue
        first = lines[0].strip()
        if first.endswith(":"):
            first = first[:-1]
        if not first:
            continue
        edges.setdefault(first, set()).update(callees_of(txt))
    return edges


def transitive_closure(edges, start):
    """All symbols reachable from start through fixture edges.  Targets without
    a fixture of their own are included as leaves; the closure stops there (we
    have no body to recurse into -- a genuine leaf in the doc's sense)."""
    seen = set()
    stack = [start]
    while stack:
        cur = stack.pop()
        for tgt in edges.get(cur, ()):
            if tgt not in seen and tgt != start:
                seen.add(tgt)
                stack.append(tgt)
    return seen


def startable(edges, witnessed, sym):
    return all(t in witnessed for t in transitive_closure(edges, sym))


# -- three-state classifier -------------------------------------------------------
def state_of(sym, rows, spec_syms):
    if sym in rowed_symbols(rows):
        return "rowed"
    if sym in spec_syms:
        return "present-but-unrowed"
    return "absent"


def suffix_family_of(sym, spec_syms):
    """Which SPEC_SUFFIX convention the symbol's theorems use (longest match wins).

    Mechanical proxy for the middle-bucket sub-split.  Fn_spec / Flat_spec are
    Fn-structured SAsm specs (a routine claim, but via the Fn layer);_fnspec is
    the attribute-family twin; _spec_within is the direct cpsTripleWithin family
    (the paneled twins' convention); plain _spec is ambiguous -- step/partial
    lemmas and whole-routine specs both use it, so it is the family that ALWAYS
    needs the theorem read.  Never treat this as a registrability verdict.
    """
    fams = [t[1] for t in spec_syms.get(sym, set())]
    for suf in SPEC_SUFFIXES:  # SPEC_SUFFIXES order, first match wins
        if any(thm.endswith(suf) for thm in fams):
            return suf
    return "(none)"


# -- statement-shape classifier (#12226) ------------------------------------------
# The suffix family above names the CONVENTION, not the STATEMENT.  Only a
# whole-routine triple anchored to the guest image can carry a Routines.lean row,
# and #12231 found five allowlist entries labelled otherwise: theorems that ARE
# `cpsTripleWithin` entry->ret, but over `CodeReq.ofProg base (body.flatten base)`
# with `base` universally quantified -- a position-independent claim about the
# SAsm body, NOT about the bytes at `GuestAddrs.<sym>`.  Rowing one silently
# vouches for code the theorem never mentions, so that class gets its OWN bucket
# (`structured-only`) instead of being folded into whole-routine.
#
# Five buckets:
#   whole-routine    entry resolves to GuestAddrs.<sym> (no offset), the CodeReq
#                    is anchored at that same address, and the exit is a return
#                    -- the rowable class.
#   structured-only  a real entry->ret cpsTripleWithin, but the entry/CodeReq are
#                    a free base: needs a linking lemma to the guest image first.
#   fragment         entry or exit is an interior pc (GuestAddrs.<sym> + k) -- a
#                    block lemma inside the routine.  Real proof, never rowable.
#   model-only       no cpsTripleWithin at all (the `(fn ...).Spec base` class).
#   needs-read       parse failed -- the honest residue.
SHAPE_ORDER = ("whole-routine", "structured-only", "fragment", "model-only", "needs-read")

_DEF_HEAD = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*(?:abbrev|def)\s+([A-Za-z_][\w'!?]*)",
    re.M)
_OPENERS, _CLOSERS = "([{⟨", ")]}⟩"


def _scan_top_level(text, needle):
    """Index of the first `needle` occurring at bracket depth 0, else None.
    `:` must not be the `:` of a `:=`; callers pass needle=':' and we skip those."""
    depth = 0
    i = 0
    while i < len(text):
        c = text[i]
        if c in _OPENERS:
            depth += 1
        elif c in _CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(needle, i):
            if needle == ":" and text.startswith(":=", i):
                i += 2
                continue
            return i
        i += 1
    return None


def def_bodies(text):
    """name -> single-line-normalised body, for `abbrev`/`def` declarations.

    Bodies are multi-line and indented; a declaration ends at the next line
    starting in column 0.  Resolution is FILE-LOCAL first at the call sites
    below: `ltPBase` is defined in both Bls12KzgLtBeSAsm.lean and the p256
    twin, and a global-first map resolves p256_lt_be's anchor to
    `GuestAddrs.blsk_lt_be` -- the shadowing trap that makes a wrong symbol
    look correctly anchored."""
    out = {}
    for m in _DEF_HEAD.finditer(text):
        nxt = re.search(r"^\S", text[m.end():], re.M)
        chunk = text[m.end(): m.end() + nxt.start()] if nxt else text[m.end():]
        eq = _scan_top_level(chunk, ":=")
        if eq is None:
            continue
        out.setdefault(m.group(1), " ".join(chunk[eq + 2:].split()))
    return out


def theorem_statement(text, thm):
    """The `theorem NAME ... : <conclusion>` header text, proof stripped."""
    m = re.search(r"^\s*theorem\s+" + re.escape(thm) + r"\b", text, re.M)
    if m is None:
        return None
    rest = text[m.end():]
    cut = re.search(r":=\s*by\b|:=\s*\n|:=\s*$", rest)
    return rest[:cut.start()] if cut else rest


def conclusion_of(statement):
    """Text after the FIRST depth-0 `:` -- binders are bracketed, so their
    colons sit at depth > 0.  First, not last: a conclusion may itself contain
    a depth-0 colon (`∀ x : T, ...`)."""
    idx = _scan_top_level(statement, ":")
    if idx is None:
        return None
    return " ".join(statement[idx + 1:].split())


def split_app_args(app):
    """Top-level argument tokens of a function application."""
    out, cur, depth = [], "", 0
    for c in app:
        if c in _OPENERS:
            depth += 1
            cur += c
        elif c in _CLOSERS:
            depth -= 1
            cur += c
        elif c.isspace() and depth == 0:
            if cur.strip():
                out.append(cur.strip())
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur.strip())
    return out


def _strip(tok):
    t = tok.strip()
    while t.startswith("(") and t.endswith(")") and _scan_top_level(t[1:-1], ")") is None:
        t = t[1:-1].strip()
    return re.sub(r"\s*:\s*Word\s*$", "", t).strip()


_IDENT = re.compile(r"[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*")


def resolve_tok(tok, local, glob, ambig):
    """Expand names to a fixpoint, file-local first, then the unambiguous globals.

    Whole-token resolution is not enough: `msetMemcpyCode` expands to
    `CodeReq.ofProg msetMemcpyBase ...`, and the anchor only becomes visible
    after `msetMemcpyBase` is expanded IN PLACE.  Returns (expanded, unresolved)
    where `unresolved` names are ambiguous ones we refused to guess at.

    Program listings are left alone: we only need to see whether a
    `GuestAddrs.<sym>` anchor appears, and expanding a 400-instruction Program
    buys nothing but blowup.  The cap must still clear a CodeReq UNION, though
    (`pdCr` chains ten `CodeReq.ofProg` legs and its own routine's anchor is one
    of them) -- so it sits above union size and below listing size."""
    expr = _strip(tok)
    unresolved = set()
    for _ in range(5):
        changed = False

        def sub(m):
            nonlocal changed
            name = m.group(0)
            if "." in name:          # keep `GuestAddrs.foo` intact -- it IS the anchor
                return name
            body = local.get(name)
            if body is None:
                if name in ambig:
                    unresolved.add(name)
                    return name
                body = glob.get(name)
            if body is None or len(body) > 2000:
                return name
            changed = True
            return "(" + body + ")"

        expr = _IDENT.sub(sub, expr)
        if not changed or len(expr) > 20000:
            break
    return _strip(expr), unresolved


def _anchor_hit(resolved, sym):
    """Does the resolved token name this symbol's guest address at all?"""
    return re.search(r"GuestAddrs\." + re.escape(sym) + r"\b", resolved) is not None


def _has_offset(resolved, sym):
    """`GuestAddrs.<sym> + k` -- an interior pc, not the entry."""
    return re.search(r"GuestAddrs\." + re.escape(sym) + r"\b[^+]*\+\s*\w", resolved) is not None


def shape_of_theorem(sym, statement, local, glob, ambig):
    """(shape, note) for one theorem statement.  See SHAPE_ORDER."""
    concl = conclusion_of(statement)
    if concl is None:
        return "needs-read", "no top-level ':' in statement"
    if "cpsTripleWithin" not in concl:
        if "cpsBranchWithin" in concl:
            return "fragment", "cpsBranchWithin (two-exit block lemma)"
        return "model-only", "no cpsTripleWithin in the conclusion"
    app = concl[concl.index("cpsTripleWithin"):]
    args = split_app_args(app)
    if len(args) < 5:
        return "needs-read", "cpsTripleWithin under-applied"

    # Binder hypotheses `(h : base = <addr>)` pin an otherwise-free variable.
    # Fold them into the resolution map so nested occurrences resolve too --
    # `CodeReq.ofProg base prog` only shows its anchor once `base` is rewritten
    # INSIDE the application, not just when it is the whole token.
    binders = statement[:statement.index(concl)] if concl in statement else statement
    pinned = dict(local)
    for hv, hrhs in re.findall(r":\s*([A-Za-z_][\w']*)\s*=\s*([^)\n]+)", binders):
        pinned.setdefault(hv, hrhs.strip())

    entry, u1 = resolve_tok(args[2], pinned, glob, ambig)
    exit_, u2 = resolve_tok(args[3], pinned, glob, ambig)
    creq, u3 = resolve_tok(args[4], pinned, glob, ambig)
    unresolved = u1 | u2 | u3

    if _has_offset(entry, sym) or _has_offset(exit_, sym):
        return "fragment", "entry/exit is an interior pc (GuestAddrs.%s + k)" % sym
    if _anchor_hit(entry, sym) and _anchor_hit(creq, sym):
        return "whole-routine", "entry + CodeReq both anchored at GuestAddrs.%s" % sym
    if unresolved:
        # A name defined in several files (ltPBase lives in four).  Guessing one
        # anchors the theorem to some OTHER routine's address -- refuse instead.
        return "needs-read", "ambiguous name(s) %s -- defined in >1 file" % ",".join(
            sorted(unresolved))
    other = re.search(r"GuestAddrs\.(\w+)", creq)
    if _anchor_hit(entry, sym) and other:
        return "needs-read", ("entry at GuestAddrs.%s but CodeReq anchored at "
                              "GuestAddrs.%s -- read it" % (sym, other.group(1)))
    if _anchor_hit(entry, sym):
        return "structured-only", "entry anchored, CodeReq is not (%s)" % creq[:44]
    return "structured-only", "position-independent base (%s)" % entry[:44]


def shape_of_symbol(sym, spec_syms, file_cache, glob, ambig):
    """Best shape over all of a symbol's spec theorems, with the winning theorem.

    Best-of, because a symbol commonly carries both an Fn-layer model spec and a
    machine triple; the strongest statement decides what the symbol needs next."""
    best = None
    for rel, thm in sorted(spec_syms.get(sym, set())):
        text = file_cache.get(rel)
        if text is None:
            text = (REPO / rel).read_text(errors="replace")
            file_cache[rel] = text
        statement = theorem_statement(text, thm)
        if statement is None:
            cand = ("needs-read", "statement not found in %s" % rel, thm)
        else:
            local = def_bodies(text)
            shape, note = shape_of_theorem(sym, statement, local, glob, ambig)
            cand = (shape, note, thm)
        if best is None or SHAPE_ORDER.index(cand[0]) < SHAPE_ORDER.index(best[0]):
            best = cand
    return best if best is not None else ("needs-read", "no spec theorem found", None)


def global_def_bodies():
    """(unambiguous map, ambiguous names).  File-local always wins.

    A name defined identically in several files is fine; a name with DIFFERENT
    bodies per file is poison.  `ltPBase` is four different guest addresses
    (blsk_lt_be / blsg_lt_p / p256_lt_be / bnf_lt_p) and `mulCr` is three (one
    of them `0x1000`, in a demo file).  Resolving those globally picks whichever
    file sorted first and reports one routine's triple as anchored at another's
    address -- so they are excluded and reported as needs-read instead.
    `GuestAddrs.lean` is skipped entirely: its bare `def <sym> : Nat := 0x...`
    would rewrite the very anchors we are looking for."""
    seen = {}
    for path in sorted(REPO.glob("EvmAsm/**/*.lean")):
        if path.name == "GuestAddrs.lean":
            continue
        for name, body in def_bodies(path.read_text(errors="replace")).items():
            seen.setdefault(name, set()).add(body)
    glob = {n: next(iter(b)) for n, b in seen.items() if len(b) == 1}
    ambig = {n for n, b in seen.items() if len(b) > 1}
    return glob, ambig


# -- doc staleness gate (advisory; --strict to fail) ------------------------------
# Table rows are  `| # | `symbol` (annotation; ...) |`.  The annotation is
# 'leaf; ...' or 'all callees verified: ...'.  We only dispute a claim that the
# symbol is STARTABLE today; 'routine REMOVED' rows (amsterdam_blob_gas_price)
# and runners-up prose are not table rows.
_TABLE_ROW = re.compile(
    r"^\|\s*\d+\s*\|\s*`([A-Za-z_][A-Za-z0-9_]*)`\s*\((.*?)\)",
    re.M,
)


def doc_table_claims():
    claims = {}
    for m in _TABLE_ROW.finditer(DOC.read_text(errors="replace")):
        sym, annotation = m.group(1), m.group(2)
        if "REMOVED" in annotation:
            continue
        claims[sym] = annotation
    return claims


def main():
    ap = argparse.ArgumentParser(description="startable proof frontier census")
    ap.add_argument("--strict", action="store_true",
                    help="fail on doc/census disagreement")
    ap.add_argument("--self-test", action="store_true",
                    help="run the classifier self-test and exit")
    ap.add_argument("--shape", action="store_true",
                    help="print the per-symbol statement-shape table for the "
                         "present-but-unrowed bucket and exit")
    args = ap.parse_args()

    if args.self_test:
        run_self_test()
        return 0

    rows = parse_routines(ROUTINES.read_text(errors="replace"))
    rowed = rowed_symbols(rows)
    witnessed = witnessed_symbols(rows)
    corr = correspondence_symbols(CORR.read_text(errors="replace"))
    spec = spec_bearing_syms()
    links = linked_symbols(GUEST_ADDRS.read_text(errors="replace"))
    fixtures = manifest_symbols()
    edges = fixture_edges()

    universe = sorted(fixtures | rowed | corr)
    states = {s: state_of(s, rows, spec) for s in universe}

    n_absent = sum(1 for s in universe if states[s] == "absent")
    n_present = sum(1 for s in universe if states[s] == "present-but-unrowed")
    n_rowed = sum(1 for s in universe if states[s] == "rowed")

    print(f"census universe: {len(universe)} symbols "
          f"(fixtures {len(fixtures)}, rowed {len(rowed)}, correspondence {len(corr)})\n")
    print("THREE-STATE COUNTS (never collapsed):")
    print(f"  rowed                : {n_rowed}")
    print(f"  present-but-unrowed  : {n_present}   <-- UPPER BOUND on the registrable "
          "class only, and NOT a work queue; split below")
    print(f"  absent               : {n_absent}\n")

    # Sub-split the middle bucket.  Present-but-unrowed mixes WHOLE-ROUTINE TRIPLES
    # (registrable, could carry a row like account_is_eip161_empty) with STEP /
    # PARTIAL / Fn-structured lemmas that are not a routine claim at all and can
    # never carry a row.  Suffix family is a mechanical proxy; whether a member is
    # genuinely registrable ALWAYS needs the theorem read.  Do not sum these into
    # a promise that N registrations are waiting.
    n_by_family = {
        "Fn_spec": 0, "_fnspec": 0, "Flat_spec": 0,
        "_spec_within": 0, "_spec": 0, "(none)": 0,
    }
    for sym in universe:
        if states[sym] != "present-but-unrowed":
            continue
        fam = suffix_family_of(sym, spec)
        n_by_family[fam] = n_by_family.get(fam, 0) + 1
    print("  present-but-unrowed, BY THEOREM FAMILY (naming convention only -- "
          "the NAME, not the statement; see the shape split below):")
    for fam in ("_spec_within", "Fn_spec", "Flat_spec", "_fnspec", "_spec", "(none)"):
        print(f"    {fam:<14} : {n_by_family.get(fam, 0)}")
    print()

    # Statement-shape split (#12226): mechanical, from the theorem's CONCLUSION.
    unrowed_syms = [s for s in universe if states[s] == "present-but-unrowed"]
    glob, ambig = global_def_bodies()
    file_cache = {}
    shapes = {s: shape_of_symbol(s, spec, file_cache, glob, ambig)
              for s in unrowed_syms}
    n_by_shape = {k: 0 for k in SHAPE_ORDER}
    for s in unrowed_syms:
        n_by_shape[shapes[s][0]] += 1
    print("  present-but-unrowed, BY STATEMENT SHAPE (parsed conclusion; only "
          "whole-routine can carry a row):")
    for sh in SHAPE_ORDER:
        tag = {
            "whole-routine": "<-- rowable today",
            "structured-only": "<-- real triple, but NOT anchored to the guest image",
            "fragment": "<-- block lemma, never rowable",
            "model-only": "<-- no machine triple at all",
            "needs-read": "<-- the honest residue",
        }[sh]
        print(f"    {sh:<16} : {n_by_shape[sh]:>3}   {tag}")
    print("  (spot-check every whole-routine claim at row time; the shape parser "
          "is a queue, not an oracle)")
    print()

    if args.shape:
        print(f"{'symbol':<34} {'shape':<16} {'theorem':<38} why")
        for sym in sorted(unrowed_syms, key=lambda s: (SHAPE_ORDER.index(shapes[s][0]), s)):
            sh, note, thm = shapes[sym]
            print(f"{sym:<34} {sh:<16} {str(thm):<38} {note}")
        return 0

    # Frontier queue: startable, not rowed, has a fixture body.
    frontier = []
    for sym in sorted(fixtures):
        if sym in rowed:
            continue
        if not startable(edges, witnessed, sym):
            continue
        in_deg = sum(1 for tg in edges.values() if sym in tg)
        frontier.append((sym, in_deg, states[sym]))

    # rank by in-degree desc, then symbol
    frontier.sort(key=lambda t: (-t[1], t[0]))

    print(f"STARTABLE FRONTIER: {len(frontier)} routines "
          "(startable, not yet rowed; ranked by caller in-degree)\n")
    print(f"{'symbol':<38} {'in-deg':>6}  {'state':<18} {'linked':>6}  theorem / correspondence")
    for sym, in_deg, st in frontier:
        thm = next(iter(sorted(spec.get(sym, [])))) if sym in spec else ""
        corr_row = "corr" if sym in corr else ""
        link = "yes" if sym in links else "no"
        col = f" {thm}  {corr_row}".rstrip()
        print(f"{sym:<38} {in_deg:>6}  {st:<18} {link:>6}  {col}")

    present_unrowed_in_frontier = sum(1 for _s, _d, st in frontier if st == "present-but-unrowed")
    print(f"\nof the {len(frontier)} frontier rows, {present_unrowed_in_frontier} are "
          "present-but-unrowed (proof exists, needs only a row)")

    # Admiral gate: --strict fails on a claimed-startable symbol that isn't.
    mismatches = []
    for sym, annotation in sorted(doc_table_claims().items()):
        if sym in rowed:
            continue
        is_claim_startable = ("leaf" in annotation or "all callees verified" in annotation)
        if is_claim_startable and not startable(edges, witnessed, sym):
            mismatches.append((sym, annotation))
    if mismatches:
        print("\nDOC vs CENSUS DISAGREEMENT (doc claims startable, census says not):")
        for sym, ann in mismatches:
            print(f"  {sym}: doc says \"{ann}\"")
        if args.strict:
            print("\n(not editing the doc; --strict makes this a failure)")
            return 1

    print("\n(advisory: exit 0 by default; pass --strict to fail on doc/census "
          "disagreement)")
    return 0


def run_self_test():
    """Plant a synthetic case in each of the three states and assert the
    classifier buckets them right; also exercise every naming convention."""
    problems = []

    def check(cond, msg):
        if not cond:
            problems.append(msg)

    # 1. naming-convention scan must see every convention...
    synthetic_theorems = {
        "header_extract_state_root_fnspec",
        "reb_spec_within",
        "bgvU32leFlat_spec",
        "bahU32leFn_spec",
        "rlpListNthItem_spec",
    }
    ok = all(SPEC_RE.search(f"theorem {t} : True := by trivial") for t in synthetic_theorems)
    check(ok, "SPEC_RE misses one of the naming conventions")
    # ...and must NOT fire on helper/inspection theorems.
    check(not SPEC_RE.search("theorem inspection_helper : True := by trivial"),
          "SPEC_RE matched a non-spec theorem 'inspection_helper'")
    check(not SPEC_RE.search("theorem specialised_thing : True := by trivial"),
          "SPEC_RE matched a non-spec theorem 'specialised_thing'")

    # 2. suffix-strip recovers the census symbol.
    check(style_snake_of_theorem("header_extract_state_root_fnspec") == "header_extract_state_root",
          "suffix strip _fnspec")
    check(style_snake_of_theorem("bgvU32leFlat_spec") == "bgv_u32le",
          "suffix strip Flat_spec + camel")
    check(style_snake_of_theorem("reb_spec_within") == "reb",
          "suffix strip _spec_within")
    check(style_snake_of_theorem("inspection_helper") is None,
          "non-spec theorem should not map to a symbol")

    # 3. three-state classifier plants one case per state.
    # synthetic_absent: no theorem, no row -> absent
    # synthetic_unrowed: theorem, no row -> present-but-unrowed (the actionable class)
    # synthetic_rowed: theorem + row -> rowed
    synthetic_rows = [
        ("synthetic_rowed", "proven", "synthetic_rowed_spec_within"),
    ]
    synthetic_spec = {
        "synthetic_unrowed": {("EvmAsm/Synthetic.lean", "synthetic_unrowed_spec_within")},
        "synthetic_rowed": {("EvmAsm/Synthetic.lean", "synthetic_rowed_spec_within")},
    }
    check(state_of("synthetic_absent", synthetic_rows, synthetic_spec) == "absent",
          "state_of(synthetic_absent) != absent")
    check(state_of("synthetic_unrowed", synthetic_rows, synthetic_spec) == "present-but-unrowed",
          "state_of(synthetic_unrowed) != present-but-unrowed")
    check(state_of("synthetic_rowed", synthetic_rows, synthetic_spec) == "rowed",
          "state_of(synthetic_rowed) != rowed")

    # 4. tail-call edge extraction: the exact derive_withdrawal_requests shape
    # (spaces before the trailing comment) must produce a stage_system_call edge.
    stub = "derive_withdrawal_requests:\n" \
           "  mv a0, a0\n" \
           "  j stage_system_call          # tail call: ...\n"
    check(callees_of(stub) == {"stage_system_call"},
          "tail-call regex missed the spaces-before-comment form")

    # 5. startable/closure: leaf is startable; a routine calling an unwitnessed
    # symbol is not.
    edges = {
        "leaf_synthetic": set(),
        "calls_unproven": {"unproven_callee"},
        "calls_proven": {"proven_callee"},
    }
    witnessed = {"proven_callee"}
    check(startable(edges, witnessed, "leaf_synthetic"),
          "genuine leaf must be startable")
    check(not startable(edges, witnessed, "calls_unproven"),
          "closure over an unwitnessed callee must not be startable")
    check(startable(edges, witnessed, "calls_proven"),
          "closure over a witnessed callee must be startable")

    # 6. statement-shape classifier (#12226): one planted case per bucket.
    # Binders are bracketed, so the conclusion starts at the FIRST depth-0 ':'.
    check(conclusion_of(" (a : Word) (h : a = b) : cpsTripleWithin n a r cr P Q")
          == "cpsTripleWithin n a r cr P Q",
          "conclusion_of must split at the first depth-0 ':' (binders are bracketed)")
    check(conclusion_of(" (a : Word) : ∀ x : Nat, P x") == "∀ x : Nat, P x",
          "conclusion_of must not split on a depth-0 ':' INSIDE the conclusion")
    check(split_app_args("f a (g b c) ⟨d, e⟩") == ["f", "a", "(g b c)", "⟨d, e⟩"],
          "split_app_args must respect brackets")

    # multi-line def body, the `pdCr`-style CodeReq union shape.
    bodies = def_bodies(
        "def someCr : CodeReq :=\n"
        "  (CodeReq.ofProg (GuestAddrs.synthetic_sym : Word) synthetic_prog).union\n"
        "    (CodeReq.ofProg (GuestAddrs.other : Word) other_prog)\n"
        "def next : Nat := 1\n")
    check("someCr" in bodies and "GuestAddrs.synthetic_sym" in bodies["someCr"],
          "def_bodies must capture a multi-line body up to the next column-0 decl")
    check(bodies.get("next") == "1", "def_bodies must capture the following decl too")

    def shape(stmt, local=None, glob=None, ambig=None, sym="synthetic_sym"):
        return shape_of_theorem(sym, stmt, local or {}, glob or {}, ambig or set())[0]

    check(shape(" (r : Word) : cpsTripleWithin 5 (GuestAddrs.synthetic_sym : Word) r "
                "(CodeReq.ofProg (GuestAddrs.synthetic_sym : Word) p) P Q")
          == "whole-routine", "anchored entry + anchored CodeReq must be whole-routine")
    check(shape(" (base r : Word) : cpsTripleWithin 5 base r "
                "(CodeReq.ofProg base (body.flatten base)) P Q")
          == "structured-only",
          "a position-independent base must NOT be reported rowable (#12231)")
    check(shape(" (r : Word) : cpsTripleWithin 5 (GuestAddrs.synthetic_sym + 12) r "
                "(CodeReq.ofProg (GuestAddrs.synthetic_sym : Word) p) P Q")
          == "fragment", "an interior entry pc must be a fragment")
    check(shape(" (base : Word) : (synthFn a b).Spec base") == "model-only",
          "an Fn-layer .Spec claim has no machine triple")
    check(shape(" (r : Word) : cpsTripleWithin 5 ambigBase r ambigCr P Q",
                ambig={"ambigBase", "ambigCr"}) == "needs-read",
          "a name defined in >1 file must be refused, not guessed")
    # the shadowing trap itself: file-local must beat a conflicting global.
    check(shape(" (r : Word) : cpsTripleWithin 5 localBase r "
                "(CodeReq.ofProg localBase p) P Q",
                local={"localBase": "(GuestAddrs.synthetic_sym : Word)"},
                glob={"localBase": "(GuestAddrs.WRONG : Word)"}) == "whole-routine",
          "file-local resolution must win over a conflicting global (ltPBase)")
    # a bare entry variable pinned by a hypothesis still counts as anchored.
    check(shape(" (base r : Word) (hbase : base = GuestAddrs.synthetic_sym) : "
                "cpsTripleWithin 5 base r (CodeReq.ofProg base p) P Q")
          == "whole-routine", "a hypothesis-pinned entry must resolve")

    if problems:
        for p in problems:
            print(f"SELF-TEST FAIL: {p}")
        sys.exit(1)
    print("self-test PASS: naming conventions (fnspec/Fn_spec/Flat_spec/"
          "_spec_within/_spec) recognised, all three states recognised, "
          "tail-call form recognised, startable closure recognised, "
          "all five statement shapes recognised (incl. the structured-only "
          "class and file-local shadowing).")


if __name__ == "__main__":
    sys.exit(main())