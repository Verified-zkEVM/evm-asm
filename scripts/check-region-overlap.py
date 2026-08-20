#!/usr/bin/env python3
"""Region-overlap gate (GH: e3c 12534 incident; coord-ordered 2026-08-19).

check-region-map.sh proved section extents, pins, the union-arena offsets and
the BAL ratchet — but never whether two declared areas overlap, and never
whether linked .bss symbols flow into a constant-defined window.  The incident
class: a 41000-byte recursive frame landed at 0xa1908780 = exactly
STORAGE_READS_AREA and silently overwrote live BAL storage-read rows; every
existing check stayed green.

This gate closes the structural hole from the *linked ELF* side:

  1. FINE-TIER cross-list pairwise disjointness.  The kernel proves each list
     internally (guestRegionMap, schemeAAnchors, frameRuntimeRegions,
     dataUnionChildren) but never across lists; a new allocation added to no
     list is ranged over nothing at all.  We check the union
     schemeAAnchors U {call_frame_arena, evm_memory_pool} U dataUnionChildren
     pairwise, excluding the documented aliasedPairs (call_frame_arena vs its
     five union children — phase-ownership overlap, RegionMap.lean aliasedPairs).
  2. SYMBOL-VS-INTERVAL reality.  STORAGE_READS_AREA and friends are numbers
     in emitted code, not ELF reservations: the linker cannot avoid them.
     Every linked symbol whose address falls strictly inside a fine-tier
     interval must be a declared member of that interval (the five union
     children inside call_frame_arena); anything else is an undeclared
     allocation squatting on a declared window — the incident class itself.

Sources of truth are the declarations in RegionMap.lean (+ the numeric defs
they resolve through: RegionMapLinkPins.lean, CallFrameLayout.lean,
BlockVerdictParams.lean, MemoryLayout.lean) and the *linked* ELF symbol table
(never recorded pins — they decay, GH #12386).

Self-test (planted defect, check-guest-image-program-bytes pattern): a gate
never seen to fail is indistinguishable from one that cannot fail.  --self-test
plants the exact incident (rlp_recursive_frame @0xa1908780, 41000 bytes) and a
declared-vs-declared overlap against the real parsed declarations and asserts
both are rejected.

Three-class taxonomy (state of coverage, stated rather than implied):
  CLASS 1  declared vs declared            -> caught (cross-list pairwise).
  CLASS 2  symbolized vs declared          -> caught (symbol/span legs); the
             shipped incident was this class (the frame had a label).
  CLASS 3  unlabelled AND undeclared       -> NOT caught, by construction: no
              symbol (readelf blind) and no list entry (pairwise blind).  No
              static instrument closes it; the available instrument is dynamic
              (runtime watch on an unclaimed address, SPIKE_WATCH hits==0).

Cross-tier check (GH #12671): coarse (guestRegionMap) x aspirational
(schemeAAnchors) pairwise, behind a documented-divergence allowlist RATCHET.
A pair is clean when disjoint, or when the coarse side is a section and the
anchor sits fully inside it (legitimate placement).  Any other intersection
FAILS unless the pair is INDIVIDUALLY named below with a reason — one entry
excuses exactly one pair, never a family, and an entry whose pair no longer
diverges FAILS as STALE (delete it).  This replaces the blanket in which the
single documented guestStack divergence silently skipped the whole
coarse-by-aspirational cross-tier check while .data sat inside the declared
evm_value_stack hole.

Interface rule: every interval is declared as base + size; extents are always
derived (Region.end := base + size, children as arena base + offset).  Never
accept a hand-written end address.
"""
import re
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent

ENV_FILES = [
    ROOT / "EvmAsm/Codegen/RegionMap.lean",
    ROOT / "EvmAsm/Codegen/RegionMapLinkPins.lean",
    ROOT / "EvmAsm/Codegen/CallFrameLayout.lean",
    ROOT / "EvmAsm/Codegen/Programs/BlockVerdictParams.lean",
    ROOT / "EvmAsm/Codegen/Layout.lean",
    ROOT / "EvmAsm/Stateless/MemoryLayout.lean",
]
REGION_MAP = ENV_FILES[0]

TOP_LEVEL = re.compile(r"^(?:def|abbrev|theorem|structure|instance|open|namespace|end|import|private|protected|#|/-|/--|/\-!)", re.M)


# ---------------------------------------------------------------------------
# Value environment: (def|abbrev) NAME : Nat|Word := <arith expr over names>
# ---------------------------------------------------------------------------

def _strip_comments(text: str) -> str:
    """Remove Lean comments while preserving string literals (evidence strings
    contain things like `--section-start` that a naive strip would eat)."""
    out = []
    i, n = 0, len(text)
    in_str = False
    while i < n:
        c = text[i]
        if in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            j = text.find("-/", i + 2)
            i = n if j < 0 else j + 2
            # keep a newline so line-anchored regexes stay sane
            out.append("\n")
            continue
        out.append(c)
        i += 1
    return "".join(out)


DEF_RE = re.compile(r"(?:^|\n)(?:private\s+)?(?:def|abbrev)\s+(\w+)\s*:[^:=]*?:=\s*")


def parse_env():
    """name -> raw expression text, from all ENV_FILES.  Duplicates (re-export
    abbrevs like `abbrev textSizeBytes : Nat := RegionMapLinkPins.textSizeBytes`)
    are accepted only when both bodies evaluate to the same value; a genuine
    disagreement fails loudly."""
    env = {}
    dup = {}
    for path in ENV_FILES:
        text = _strip_comments(path.read_text())
        for m in DEF_RE.finditer(text):
            name = m.group(1)
            start = m.end()
            nxt = TOP_LEVEL.search(text, start)
            body = text[start : nxt.start() if nxt else len(text)]
            body = " ".join(body.split()).rstrip()
            if name in env and env[name] != body:
                dup.setdefault(name, []).append((str(path), body))
                continue
            env[name] = body
    if dup:
        bad = []
        for name, variants in dup.items():
            # The LinkPins re-export in RegionMap.lean is `abbrev X := ...X`,
            # which self-cycles under last-component resolution; the genuine
            # body is the variant that evaluates.  Prefer it, verify the rest.
            bodies = [(env[name], str(REGION_MAP))] + [(b, p) for p, b in variants]
            vals = []
            for body, path in bodies:
                try:
                    vals.append((eval_expr(body, env), body, path))
                except EvalErr:
                    continue
            if not vals:
                bad.append(f"{name}: no variant resolves")
                continue
            first = vals[0][0]
            if any(v != first for v, _, _ in vals):
                bad.append(f"{name}: variants disagree ({[(hex(v), p) for v, _, p in vals]})")
            else:
                env[name] = vals[0][1]
        if bad:
            raise SystemExit("REGION-OVERLAP GATE: inconsistent duplicate defs: " + "; ".join(bad[:6]))
    return env


TOKEN_RE = re.compile(r"\s*(?:(0x[0-9a-fA-F]+|\d+)|([A-Za-z_][A-Za-z0-9_.]*)|([-+*/()]))")


class EvalErr(Exception):
    pass


def eval_expr(expr, env, resolving=None, depth=0):
    """Evaluate a Nat expression: literals, (qualified) names, + - * / parens.
    Qualified names resolve by last component before .toNat-style suffixes."""
    toks = []
    i = 0
    while i < len(expr):
        m = TOKEN_RE.match(expr, i)
        if not m:
            raise EvalErr(f"tokenize failed at {expr[i:i+20]!r} in {expr!r}")
        i = m.end()
        if m.group(1):
            toks.append(("num", int(m.group(1), 0)))
        elif m.group(2):
            toks.append(("id", m.group(2)))
        elif m.group(3):
            toks.append(("op", m.group(3)))
        else:
            raise EvalErr(f"empty token in {expr!r}")
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else (None, None)

    def take():
        nonlocal pos
        t = toks[pos]
        pos += 1
        return t

    def resolve(name):
        parts = name.split(".")
        cands = [p for p in parts if p not in ("toNat",)]
        base = cands[-1] if cands else name
        if base not in env:
            raise EvalErr(f"unresolved identifier {name!r} (last component {base!r})")
        if depth > 64 or len(resolving or ()) > 64:
            raise EvalErr(f"resolution cycle/too deep at {name!r}")
        if base in (resolving or set()):
            raise EvalErr(f"cycle resolving {name!r}")
        return eval_expr(env[base], env, (resolving or set()) | {base}, depth + 1)

    def parse_primary():
        kind, val = take()
        if kind == "num":
            return val
        if kind == "id":
            return resolve(val)
        if kind == "op" and val == "(":
            v = parse_add()
            k2, v2 = take()
            if k2 != "op" or v2 != ")":
                raise EvalErr(f"expected ) in {expr!r}")
            return v
        raise EvalErr(f"unexpected token {kind} {val!r} in {expr!r}")

    def parse_mul():
        v = parse_primary()
        while True:
            k, op = peek()
            if k == "op" and op in "*/":
                take()
                rhs = parse_primary()
                v = v * rhs if op == "*" else v // rhs
            else:
                return v

    def parse_add():
        v = parse_mul()
        while True:
            k, op = peek()
            if k == "op" and op in "+-":
                take()
                rhs = parse_mul()
                v = v + rhs if op == "+" else v - rhs
            else:
                return v

    v = parse_add()
    if pos != len(toks):
        raise EvalErr(f"trailing tokens in {expr!r}")
    return v


# ---------------------------------------------------------------------------
# Region record parsing
# ---------------------------------------------------------------------------

class Region:
    def __init__(self, name, base, size, origin):
        self.name, self.base, self.size, self.origin = name, base, size, origin

    @property
    def end(self):
        return self.base + self.size

    def __repr__(self):
        return f"{self.name}[{self.base:#x}..{self.end:#x})"


FIELD_RE = re.compile(r"(name|base|size|off)\s*:=\s*([^,\n]+)")


def parse_records(block, env, origin):
    """Parse `{ name := "...", base := <expr>, size := <expr>, ... },` records."""
    out = []
    for rm in re.finditer(r"\{([^{}]*)\}", block):
        rec = rm.group(1)
        fields = {}
        for fm in FIELD_RE.finditer(rec):
            key, val = fm.group(1), fm.group(2).strip().rstrip(",").rstrip()
            if key not in fields:
                fields[key] = val
        if "name" not in fields or ("base" not in fields and "off" not in fields):
            continue
        name = fields["name"].strip().strip('"')
        try:
            if "base" in fields:
                base = eval_expr(fields["base"], env)
                size = eval_expr(fields["size"], env)
                out.append(Region(name, base, size, origin))
            else:
                off = eval_expr(fields["off"], env)
                size = eval_expr(fields["size"], env)
                out.append(Region(name, off, size, origin))
        except EvalErr as e:
            raise SystemExit(f"REGION-OVERLAP GATE: cannot evaluate record {name!r} in {origin}: {e}")
    return out


def def_block(text, name):
    m = re.search(
        rf"(?:^|\n)(?:private\s+)?(?:def|abbrev)\s+{name}\b"
        rf"(?:\s*\([^\n]*?\))?\s*:[^:=]*?:=", text)
    if not m:
        raise SystemExit(f"REGION-OVERLAP GATE: cannot find def {name!r} in {REGION_MAP}")
    nxt = TOP_LEVEL.search(text, m.end())
    return text[m.end() : nxt.start() if nxt else len(text)]


def load_declarations():
    env = parse_env()
    text = _strip_comments(REGION_MAP.read_text())

    coarse_names = ["inputRegion", "ziskSystemRegion", "outputRegion", "guestStackRegion",
                    "stateTrackerLiveRegion", "textRegion", "dataRegion", "bssRegion",
                    "stateGasDiagRegion", "sszScratchRegion"]
    coarse = []
    for cn in coarse_names:
        blk = def_block(text, cn)
        recs = parse_records(blk, env, cn)
        if len(recs) != 1:
            raise SystemExit(f"REGION-OVERLAP GATE: {cn} yielded {len(recs)} records, expected 1")
        coarse.extend(recs)
    # `rlpRecursiveFrameRegion` is an abbrev over the parameterized
    # `rlpRecursiveFrameRegionForCap`; instantiate the latter at the policy cap
    # so the emitted frame section participates in the same coarse interval
    # census as the other guest regions.
    frame_block = def_block(text, "rlpRecursiveFrameRegionForCap")
    # The size field applies the one parameterized arithmetic helper.  The
    # small parser above intentionally handles constants, not Lean function
    # applications, so substitute that helper's source body before applying
    # the policy-cap argument.  Keep this explicit: changing the helper's
    # formula must make this gate's source-level substitution stale and
    # visible, rather than silently treating the application as a constant.
    frame_block = frame_block.replace(
        "rlpRecursiveDecodeFrameBytes depthCap", "(40 * depthCap + 40)"
    )
    frame_block = frame_block.replace("depthCap", "rlpRecursiveDecodeDepthCap")
    frame_recs = parse_records(frame_block, env, "rlpRecursiveFrameRegion")
    if len(frame_recs) != 1:
        raise SystemExit(
            f"REGION-OVERLAP GATE: rlpRecursiveFrameRegion yielded {len(frame_recs)} records, expected 1")
    coarse.extend(frame_recs)

    scheme_a = parse_records(def_block(text, "schemeAAnchors"), env, "schemeAAnchors")
    # frameRuntimeRegions = [ inline call_frame_arena record, evmMemoryPoolRegion ]
    # (a bare name reference to the named def below it).
    frame_rt = parse_records(def_block(text, "frameRuntimeRegions"), env, "frameRuntimeRegions")
    frame_rt += parse_records(def_block(text, "evmMemoryPoolRegion"), env, "evmMemoryPoolRegion")
    arena_base = eval_expr("callFrameArenaBase", env)
    children_rel = parse_records(def_block(text, "dataUnionChildren"), env, "dataUnionChildren")
    children = [Region(c.name, arena_base + c.base, c.size, "dataUnionChildren") for c in children_rel]

    expected = (11, 17, 2, 5)
    got = (len(coarse), len(scheme_a), len(frame_rt), len(children))
    if got != expected:
        raise SystemExit(
            f"REGION-OVERLAP GATE: declaration census changed (coarse, schemeA, frame, children) "
            f"= {got}, expected {expected} — update this gate's expectations consciously")
    return env, coarse, scheme_a, frame_rt, children


# ---------------------------------------------------------------------------
# ELF symbol table
# ---------------------------------------------------------------------------

RAM_LO, RAM_HI = 0xA0000000, 0xC0000000


def load_symbols(elf):
    out = subprocess.run(["readelf", "-sW", str(elf)], capture_output=True, text=True, check=True)
    syms = []
    for line in out.stdout.splitlines():
        parts = line.split()
        if len(parts) < 8:
            continue
        try:
            val = int(parts[1].removesuffix("0x") if parts[1].startswith("0x") else parts[1], 16)
            size = int(parts[2])
        except ValueError:
            continue
        name = parts[7]
        if parts[6] == "UND" or not name or not (RAM_LO <= val < RAM_HI):
            continue
        syms.append((name, val, size))
    return syms


# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------

def fmt_pair(a, b):
    return (f"OVERLAP: {a.origin}:{a.name} [{a.base:#x}..{a.end:#x}) intersects "
            f"{b.origin}:{b.name} [{b.base:#x}..{b.end:#x}) "
            f"(overlap [{max(a.base,b.base):#x}..{min(a.end,b.end):#x}))")


def check_fine_tier(scheme_a, frame_rt, children):
    aliased = {("call_frame_arena", c.name) for c in children }
    fine = scheme_a + frame_rt + children
    errs = []
    for i in range(len(fine)):
        for j in range(i + 1, len(fine)):
            a, b = fine[i], fine[j]
            if (a.name, b.name) in aliased or (b.name, a.name) in aliased:
                continue
            if a.base < b.end and b.base < a.end:
                errs.append(fmt_pair(a, b))
    return errs


# Coarse regions that are ELF sections legitimately CONTAIN aspirational
# anchors; the remaining coarse regions are live resources an anchor must
# never touch.
SECTION_REGIONS = {".text", ".data", ".bss", ".state_gas_diag", ".sszscratch"}

# Documented coarse x aspirational divergences (GH #12671 ratchet).
# One entry excuses EXACTLY ONE named pair.  An unlisted intersecting pair
# FAILS; a listed pair that no longer diverges FAILS as STALE (delete it).
# Never widen an entry into a family or a wildcard — that rebuilds the
# blanket this ratchet exists to remove.
COARSE_DIVERGENCE_ALLOWLIST = [
    ("guest_stack", "ssz_input_decoded",
     "documented guestStack divergence (RegionMap.lean "
     "guestStack_not_disjoint_from_schemeA); aspirational anchor predates "
     "the split; declaration fix tracked in RegionMap.lean"),
    ("guest_stack", "execution_witness_area",
     "documented guestStack_overlaps_executionWitnessArea (RegionMap.lean); "
     "aspirational anchor; declaration fix tracked in RegionMap.lean"),
    (".data", "evm_value_stack",
     "linker placed .data inside the declared value-stack hole "
     "(evm_frame_stack ends exactly at the value-stack base; the stack "
     "declares the whole hole to .bss base); measured never written at "
     "runtime (GH #12671); declaration fix routed to the RegionMap owner"),
    ("transient_storage_log", "state_tracker_area",
     "found by this gate's first census run (GH #12671): the aspirational "
     "state_tracker_area declares [0xa0630000..0xa0a30000) while the live "
     "coarse region transient_storage_log occupies its upper half "
     "[0xa0830000..0xa0a30000) (persistent half retired in RegionMap.lean); "
     "declaration reconciliation tracked in RegionMap.lean"),
]


def check_coarse_vs_aspirational(coarse, scheme_a):
    allow = {(a, b): reason for a, b, reason in COARSE_DIVERGENCE_ALLOWLIST}
    seen = set()
    errs = []
    for c in coarse:
        for a in scheme_a:
            if not (c.base < a.end and a.base < c.end):
                continue  # disjoint: clean
            if c.name in SECTION_REGIONS and a.base >= c.base and a.end <= c.end:
                continue  # anchor sits fully inside a section: legitimate placement
            key = (c.name, a.name)
            seen.add(key)
            if key in allow:
                continue
            errs.append(fmt_pair(c, a) + " — coarse×aspirational divergence not "
                         "in the documented allowlist; name it individually with "
                         "a reason or fix the declaration (GH #12671)")
    for key in allow:
        if key not in seen:
            errs.append(f"STALE coarse×aspirational allowlist entry "
                        f"{key[0]} × {key[1]} — the pair no longer diverges; "
                        f"delete the entry (GH #12671)")
    return errs


def check_symbols(syms, scheme_a, frame_rt, children):
    """Every symbol strictly inside a *container* interval must be a declared
    member or boundary label of that interval.

    Scope: the real constant-defined container windows (the read/write arenas
    the emitted code addresses through MemoryLayout constants — the incident
    class) plus the frame runtime arena/pool.  The five aspirational
    stack/tracker/witness anchors (ssz_input_decoded, execution_witness_area,
    state_tracker_area, evm_frame_stack, evm_value_stack) are excluded from
    symbol-level checking: their overlap with emitted reality is the known
    scheme-A P1 divergence (RegionMap.lean documents the guest_stack collision;
    the evm_value_stack-vs-.data overlap is reported separately).
    """
    containers = [r for r in scheme_a if r.name not in (
        "ssz_input_decoded", "execution_witness_area", "state_tracker_area",
        "evm_frame_stack", "evm_value_stack")]
    declared = {r.name for r in scheme_a + frame_rt + children}
    boundary = set()
    for n in declared:
        boundary |= {n, n + "_end", n + "_base"}
    # bss_lead_pad: size-0 linker filler label marking where emitted .bss
    # content yields to the container block (observed at storage_reads_area
    # base); a reservation *crossing* into a container would carry a different
    # symbol and still be caught.
    boundary |= {"bss_lead_pad"}
    members = {c.name for c in children}
    fine = containers + frame_rt + children
    errs = []
    for name, val, size in syms:
        if name in boundary:
            continue
        for r in fine:
            if r.base <= val < r.end:
                if r.name == "call_frame_arena" and name in members:
                    break
                errs.append(
                    f"UNDECLARED ALLOCATION: symbol {name!r} @ {val:#x} (size {size}) lies inside "
                    f"{r.origin}:{r.name} [{r.base:#x}..{r.end:#x})")
                break
    # dedupe, keep deterministic order
    seen, out = set(), []
    for e in errs:
        if e not in seen:
            seen.add(e)
            out.append(e)
    return out


def load_section_bounds(elf):
    """Section start/end addresses from readelf -SW — the designed free-space
    boundaries (inter-section gaps house several containers by design)."""
    out = subprocess.run(["readelf", "-SW", str(elf)], capture_output=True, text=True, check=True)
    bounds = set()
    for line in out.stdout.splitlines():
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)", line)
        if m:
            base = int(m.group(2), 16)
            size = int(m.group(4), 16)
            bounds |= {base, base + size}
    return bounds


def check_span(syms, containers, section_bounds=frozenset()):
    """Consecutive-symbol span check: within the union of same-section symbol
    addresses, the emitted content occupies the whole span between adjacent
    symbols, so a span crossing into a container means symbol-less content
    (.zero advances, unsymbolised reservations) flowed into the window even
    though no individual symbol sits inside it.

    Exemptions (measured, by design):
    - spans starting at a container base: bss_lead_pad sits at
      storage_reads_area base and the linker pads up to the pinned
      call_frame_arena, housing the read/write containers inside .bss
      counter space (zero symbols in [0xa1908780, arena base));
    - spans starting at a section boundary: the inter-section gap
      [.state_gas_diag end .. .sszscratch) houses storage_writes_undo,
      account_writes(_undo) and tx_account_writes with NO symbols at all —
      the ELF does not record those allocations either way, which is exactly
      why full coverage (obligation two) needs an .s-side instrument."""
    addrs = sorted(set((v, n) for n, v, s in syms))
    bounds = {r.base for r in containers} | set(section_bounds)
    errs = []
    for (a1, n1), (a2, n2) in zip(addrs, addrs[1:]):
        if a1 in bounds:
            continue  # designed reservation / inter-section free space
        for r in containers:
            if a1 < r.end and r.base < a2 and not (a2 <= r.base or a1 >= r.end):
                if r.base <= a1 < r.end:
                    continue  # already reported by the symbol check
                errs.append(
                    f"UNSYMBOLISED FLOW: emitted span [{n1} @ {a1:#x} .. {n2} @ {a2:#x}) "
                    f"crosses into {r.origin}:{r.name} [{r.base:#x}..{r.end:#x}) "
                    f"(symbol-less reservation inside the window)")
    return errs


def check_memlayout_coverage(intervals):
    """Obligation-one completeness: every layout-range constant declared in
    MemoryLayout.lean must lie inside some declared interval.  A constant
    outside every interval is a declared window no disjointness check ranges
    over — invisible to pairwise checks however correct they are."""
    ml = _strip_comments((ROOT / "EvmAsm/Stateless/MemoryLayout.lean").read_text())
    errs = []
    for m in re.finditer(r"(?:def|abbrev)\s+(\w+)\s*(?::\s*Word\b[^:=]*)?:=\s*(0x[0-9a-fA-F]+)", ml):
        name, val = m.group(1), int(m.group(2), 16)
        if not (0xA0000000 <= val < 0xC0000000):
            continue
        if not any(r.base <= val < r.end for r in intervals):
            errs.append(
                f"UNCOVERED DECLARATION: MemoryLayout.{name} = {val:#x} lies inside no "
                f"declared region interval — no disjointness check ranges over it")
    return errs


def check_coarse(coarse):
    errs = []
    errs = []
    for i in range(len(coarse)):
        for j in range(i + 1, len(coarse)):
            a, b = coarse[i], coarse[j]
            if a.base < b.end and b.base < a.end:
                errs.append(fmt_pair(a, b))
    return errs


# ---------------------------------------------------------------------------
# Entry points
# ---------------------------------------------------------------------------

def run(elf):
    env, coarse, scheme_a, frame_rt, children = load_declarations()
    syms = load_symbols(elf) if elf else []
    containers = [r for r in scheme_a if r.name not in (
        "ssz_input_decoded", "execution_witness_area", "state_tracker_area",
        "evm_frame_stack", "evm_value_stack")] + frame_rt + children
    errs = check_coarse(coarse) + check_fine_tier(scheme_a, frame_rt, children) \
        + check_coarse_vs_aspirational(coarse, scheme_a) \
        + check_symbols(syms, scheme_a, frame_rt, children) \
        + check_span(syms, containers, load_section_bounds(elf) if elf else frozenset()) \
        + check_memlayout_coverage(coarse + scheme_a + frame_rt + children)
    if errs:
        print("REGION-OVERLAP GATE: FAIL")
        for e in errs:
            print("  " + e)
        return 1
    print(f"REGION-OVERLAP GATE: OK "
          f"(coarse {len(coarse)} pairwise disjoint; fine tier "
          f"{len(scheme_a) + len(frame_rt) + len(children)} intervals pairwise disjoint "
          f"modulo {len(children)} documented arena aliases; "
          f"coarse×aspirational divergences = {len(COARSE_DIVERGENCE_ALLOWLIST)} "
          f"individually documented; "
          f"{len(syms)} RAM symbols checked, none inside undeclared windows)")
    return 0


def self_test():
    """Planted-defect self-test against the REAL parsed declarations."""
    env, coarse, scheme_a, frame_rt, children = load_declarations()

    # Case 1: the incident — undeclared 41000-byte frame at 0xa1908780.
    planted = [("rlp_recursive_frame", 0xA1908780, 41000)]
    errs = check_symbols(planted, scheme_a, frame_rt, children)
    ok1 = any("rlp_recursive_frame" in e and "storage_reads_area" in e for e in errs)

    # Case 2: declared-vs-declared overlap — clone storage_writes_area shifted
    # so it overlaps account_reads_area.
    victim = next(r for r in scheme_a if r.name == "account_reads_area")
    clone = Region("planted_overlap", victim.base + 0x100, 0x1000, "self-test")
    errs2 = check_fine_tier(scheme_a + [clone], frame_rt, children)

    # Case 3: clean control — the real declarations must produce no errors.
    clean = check_fine_tier(scheme_a, frame_rt, children)

    # Case 4 (GH #12671): an UNLISTED anchor touching a coarse live resource
    # must be rejected — planted anchor inside guestStackRegion.
    gs = next(r for r in coarse if r.name == "guest_stack")
    anchor = Region("planted_anchor", gs.base + 0x800, 0x100, "self-test")
    errs4 = check_coarse_vs_aspirational(coarse, scheme_a + [anchor])
    ok4 = (len(errs4) == 1 and "planted_anchor" in errs4[0] and "guest_stack" in errs4[0]
           and "not in the documented allowlist" in errs4[0])

    # Case 5 (GH #12671): an anchor fully inside a section is legitimate.
    bss = next(r for r in coarse if r.name == ".bss")
    inner = Region("planted_bss_anchor", bss.base + 0x1000, 0x100, "self-test")
    errs5 = check_coarse_vs_aspirational(coarse, scheme_a + [inner])

    # Case 6 (GH #12671): STALE ratchet — removing evm_value_stack from the
    # anchor set makes the (dataRegion, evm_value_stack) entry stale, which
    # must FAIL (an entry whose pair no longer diverges must be deleted).
    shrunk = [r for r in scheme_a if r.name != "evm_value_stack"]
    errs6 = check_coarse_vs_aspirational(coarse, shrunk)
    ok6 = any("STALE" in e and ".data × evm_value_stack" in e for e in errs6)

    # Case 7 (GH #12671): clean control — the real declarations pass the
    # cross-tier check with exactly the documented divergences.
    clean7 = check_coarse_vs_aspirational(coarse, scheme_a)

    if not ok1:
        print("SELF-TEST: FAIL — planted 0xa1908780 frame was NOT rejected")
        return 1
    if not errs2:
        print("SELF-TEST: FAIL — planted declared-vs-declared overlap was NOT rejected")
        return 1
    if clean:
        print("SELF-TEST: FAIL — real declarations fail the clean control:")
        for e in clean:
            print("  " + e)
        return 1
    if not ok4:
        print("SELF-TEST: FAIL — unlisted coarse×aspirational divergence was NOT rejected")
        return 1
    if errs5:
        print("SELF-TEST: FAIL — anchor fully inside a section wrongly rejected:")
        for e in errs5:
            print("  " + e)
        return 1
    if not ok6:
        print("SELF-TEST: FAIL — STALE allowlist entry was NOT detected")
        return 1
    if clean7:
        print("SELF-TEST: FAIL — real declarations fail the cross-tier clean control:")
        for e in clean7:
            print("  " + e)
        return 1
    print("SELF-TEST: PASS (planted frame rejected; planted overlap rejected; "
          "clean controls clean; unlisted cross-tier divergence rejected; "
          "in-section anchor accepted; STALE entry detected)")
    return 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--self-test" in args:
        sys.exit(self_test())
    elf = None
    for a in args:
        if not a.startswith("--"):
            elf = Path(a)
            break
    if elf is None:
        print("usage: check-region-overlap.py <guest.elf> | --self-test", file=sys.stderr)
        sys.exit(2)
    sys.exit(run(elf))
