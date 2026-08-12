#!/usr/bin/env python3
"""transcription_queue.py — the DEMAND-FIRST String->Program conversion queue
(GH #12035).

The two censuses this repo already has —
`docs/4ch8f-asm-to-program-coverage.md` (how a `*Function : String` is shaped)
and `docs/4ch8f-guest-image-coverage.md` (which `.text` bytes a converted
`_prog` covers) — rank nothing.  They answer "how big" and "how hard", never
"who is waiting".  Transcription ordered by either of those is transcription
ordered by COST, and the observed effect is that the routines four active
proof lanes are stalled behind stay unconverted because they are large, while
small leaves nobody is blocked on keep landing.

This script joins the guest-image census (the universe + the cost column) with
the DEMAND evidence that lives in the proof tree:

  1. obligation blockers   EvmAsm/Progress/Obligations.lean `blockedBy` entries
                           naming the routine.  Strongest signal: a symbol
                           blocking two obligation rows outranks one blocking
                           one, which outranks one blocking none.
  2. named residuals       declarations whose NAME carries `Residual` (the
                           `…ResidualNote` / `…CallWithinShape` discharge-owner
                           convention) and whose text names the routine.
  3. open proof issues     a committed snapshot of
                           `gh issue list --label proof --state open`
                           (scripts/proof-issues.json; refresh with
                           --refresh-issues).  Read from the snapshot, never
                           the network, so --write-doc is deterministic.
  4. registry gates        `.conditional` / `.execSpec` rows in
                           EvmAsm/Progress/Routines.lean whose `gate`/`notes`
                           text names the routine.
  5. call sites            emitted-instruction references (the
                           check_routine_liveness.py patterns).  Weighted, but
                           CAPPED below one obligation row: a popular leaf must
                           never outrank a named blocker.

Byte size is a COST column.  It is printed, it is never scored.

Usage:
  python3 scripts/transcription_queue.py                 # human summary + top rows
  python3 scripts/transcription_queue.py --top N         # how many rows to print
  python3 scripts/transcription_queue.py --all           # every scored symbol
  python3 scripts/transcription_queue.py --md            # markdown tables to stdout
  python3 scripts/transcription_queue.py --write-doc     # regenerate the doc
  python3 scripts/transcription_queue.py --check-doc     # drift guard (exit 1)
  python3 scripts/transcription_queue.py --refresh-issues  # ONLY network mode
  python3 scripts/transcription_queue.py --self-test     # scorer/matcher self-test
"""

import argparse
import difflib
import json
import os
import re
import subprocess
import sys

from guest_image_coverage import load_converted

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OBLIGATIONS = os.path.join(ROOT, "EvmAsm/Progress/Obligations.lean")
ROUTINES = os.path.join(ROOT, "EvmAsm/Progress/Routines.lean")
PROGRESS = os.path.join(ROOT, "EvmAsm/Progress.lean")
EVMASM = os.path.join(ROOT, "EvmAsm")
ISSUES = os.path.join(ROOT, "scripts/proof-issues.json")
DOC = os.path.join(ROOT, "docs/4ch8f-transcription-queue.md")
TEMPLATE = os.path.join(ROOT, "scripts/asm-fixtures/transcription-queue-template.md")

REPO_SLUG = "Verified-zkEVM/evm-asm"

# This queue's OWN issue.  It names the worked examples it expects to see at
# the top, so counting it as evidence would make the ranking circular — the
# queue would "discover" exactly what its specification told it to find.
# Excluded from the issue signal; the snapshot still records it.
SELF_ISSUE = 12035

# ---- weights ---------------------------------------------------------------
# Ratios, not calibrated constants.  The only property that matters is the
# ORDER they impose: one obligation row outranks any amount of call-site
# popularity, and CALLSITE_CAP * W_CALLSITE < W_OBLIGATION enforces that.
W_OBLIGATION = 100   # per distinct obligation id whose blockedBy names it
W_RESIDUAL = 40      # per distinct Residual-named declaration naming it
W_ISSUE = 25         # per distinct open proof-label issue naming it
W_GATE = 15          # per distinct .conditional/.execSpec registry row naming it
W_CALLSITE = 2       # per emitted call site, capped
CALLSITE_CAP = 30    # 30 * 2 = 60 < W_OBLIGATION, by construction

# How many rows the generated doc's headline queue and popularity tail show.
DOC_TOP = 25
DOC_TAIL_TOP = 25

# ---- declared aliases ------------------------------------------------------
# The evidence sources name routines in three vocabularies, and only one of
# them is the linker symbol:
#
#   * SPEC-SIDE names.  #11800 and obligations 7/10 say "build_node_db /
#     build_code_db"; those are `Stateless/SpecRef/WitnessState.lean` builders,
#     not guest symbols.  The guest routines that implement them are the
#     witness-index builders.
#   * OPCODE MNEMONICS.  Obligation 5 names `KECCAK256`, `SLOAD`, `CALL` …;
#     the guest symbol is the handler `h_<MNEMONIC>`.  Handled MECHANICALLY
#     (see `opcode_registry` / `opcode_context_pattern`) — the mnemonic list
#     comes from `Progress.lean`, and a mnemonic only counts where it appears
#     AS an opcode (backticked, `.opcode "…"`, or `h_…`).
#   * PROSE.  #11801 describes "the dispatcher's fetch-decode-dispatch step"
#     and "fetch/decode/table-jump as one reusable triple"; #11802 calls the
#     same thing the `execute : ExecutionSeam` parameter.  Neither writes
#     `.dispatch_loop`.
#
# Everything hand-declared lives HERE, carries a `why`, and is rendered into
# the generated doc so a reader can audit or challenge each entry rather than
# discovering it in the code.  Nothing else in this script hand-ranks anything.
IDENT_ALIASES = {
    # spec-side identifier -> (guest symbol, why)
    "build_node_db": ("witness_index_build",
                      "SpecRef `WitnessState.build_node_db`; the guest routine "
                      "that populates `node_db_buckets` from the witness "
                      "section is `witness_index_build` (#11800's target)"),
    "build_code_db": ("witness_codes_index_build",
                      "SpecRef `WitnessState.build_code_db`; the guest side is "
                      "the code-DB index builder (#11800 item 2)"),
    "dispatch_loop": (".dispatch_loop",
                      "the guest label carries a leading dot; prose writes it "
                      "without one"),
}

PROSE_ANCHORS = [
    # (regex, guest symbol, why) — matched against obligation blocker text and
    # issue title+body.  Deliberately few and specific; each one is a claim
    # that a named piece of prose is ABOUT a symbol it does not spell.
    (r"fetch[-/]decode[-/](?:dispatch|table[- ]jump)", ".dispatch_loop",
     "#11801's dispatch-step lemma is exactly the `.dispatch_loop` "
     "fetch/decode/table-jump body"),
    (r"\bExecutionSeam\b", ".dispatch_loop",
     "#11802's `execute : ExecutionSeam` parameter is instantiated by the "
     "dispatch loop plus its handlers"),
    (r"simulation bridge from dispatched handlers", ".dispatch_loop",
     "obligation 4's blocker names the bridge whose machine side is the "
     "dispatch loop"),
]


def read_source(path: str) -> str:
    """Read a tree file, tolerating a file that vanishes mid-walk (a sibling
    agent editing `EvmAsm/` under us).  A missing file contributes no evidence
    rather than aborting a census of 3000+ modules."""
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


# ---- symbol matching -------------------------------------------------------
def symbol_pattern(sym: str) -> "re.Pattern":
    """Word-boundary matcher for a guest symbol.

    The leading-dot class in the lookbehind is what keeps `dispatch_loop` from
    matching inside `.dispatch_loop` (they are separate census entries) and
    keeps `rlp_item_size` from matching inside `x.rlp_item_size`.  The trailing
    class keeps `witness_lookup_by_hash` from matching
    `witness_lookup_by_hash_indexed` — a DIFFERENT 200-byte symbol.  The cost
    of that strictness is stated in the doc's limits section: a mention that
    only ever appears as a suffixed theorem name (`<sym>_spec_within`) and
    never bare is invisible here.
    """
    return re.compile(r"(?<![A-Za-z0-9_.])" + re.escape(sym) + r"(?![A-Za-z0-9_])")


# ---- universe: the unconverted half of the guest-image census --------------
def unconverted_universe():
    """[(symbol, addr, extent_bytes)] for every `.text` symbol with no covering
    `_prog`, straight from guest_image_coverage's manifest/#guard parse.

    Deliberately NOT keyed on `GuestAddrs.lean`: that file lists `String`-only
    routines called by address and omits probe-only routines that exist, so it
    is an oracle in neither direction.  The reliable test is the one
    guest_image_coverage already makes — a manifest row bound to a
    `"<entry>:\\n" ++ emitProgram… ` Function with a kernel-checked
    `#guard <prog>.length` pin.
    """
    syms, text_end, converted = load_converted()
    out = []
    for i, (addr, name) in enumerate(syms):
        end = syms[i + 1][0] if i + 1 < len(syms) else text_end
        if name not in converted:
            out.append((name, addr, end - addr))
    return out, set(converted), len(syms)


# ---- signal 1: obligation blockers -----------------------------------------
_OBLIG_SPLIT = re.compile(r"\n  \{ id := ")
_OBLIG_ID = re.compile(r"(\d+)")
_OBLIG_STOP = re.compile(r"\n\s+(?:auditedAt|note|witness) :=")


def obligation_blocker_texts(src: str):
    """[(obligation_id, blockedBy_text)] — the blocker region ONLY.

    `note` prose routinely names routines as context ("re-audited; X is now
    .proven"), which is the opposite of a blocking claim, so scoring it would
    invert the signal.  Cut at the first auditedAt/note/witness field.
    """
    try:
        body = src.split("def obligations : List Obligation := [", 1)[1]
    except IndexError:
        sys.exit("could not find `def obligations` in Obligations.lean")
    out = []
    for rec in _OBLIG_SPLIT.split(body)[1:]:
        m = _OBLIG_ID.match(rec)
        if not m:
            continue
        oid = int(m.group(1))
        b = re.search(r"blockedBy :=", rec)
        if not b:
            continue
        blk = rec[b.end():]
        stop = _OBLIG_STOP.search(blk)
        out.append((oid, blk[:stop.start()] if stop else blk))
    return out


# ---- signal 2: named residuals ---------------------------------------------
_DECL = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure)\s+([A-Za-z0-9_'.]+)", re.M)
_RESIDUAL_NAME = re.compile(r"[Rr]esidual")
_BLOCK_CAP = 8000


def residual_blocks(paths):
    """[(qualified_decl_label, text)] for every declaration whose NAME carries
    `Residual` — the repo's discharge-owner convention (`…ResidualNote`,
    `…_residual…`).  A declaration's block runs from its own docstring (where
    the owner is actually named) to the next declaration, capped.

    Name-keyed on purpose: the word "residual" appears in thousands of lines of
    EXP loop-arithmetic prose that names no routine, and scoring free text
    would drown the signal that `…ResidualNote` exists to carry.
    """
    out = []
    for path in paths:
        txt = read_source(path)
        if "esidual" not in txt:
            continue
        rel = os.path.relpath(path, ROOT)
        starts = [(m.start(), m.group(1)) for m in _DECL.finditer(txt)]
        for i, (pos, name) in enumerate(starts):
            if not _RESIDUAL_NAME.search(name):
                continue
            doc = txt.rfind("/--", max(0, pos - 3000), pos)
            begin = doc if doc >= 0 and "-/" in txt[doc:pos] else pos
            end = starts[i + 1][0] if i + 1 < len(starts) else len(txt)
            out.append((f"{rel}:{name}", txt[begin:min(end, begin + _BLOCK_CAP)]))
    return out


# ---- signal 4: registry gates ----------------------------------------------
_ROW_SPLIT = re.compile(r"(?m)^  routine \"")
_ROW_HEAD = re.compile(r'([A-Za-z0-9_]+)"\s+\.(\w+)')
GATED_TIERS = ("conditional", "execSpec")


def registry_gate_blocks(src: str):
    """[(label, text)] for `.conditional`/`.execSpec` rows — the row's own
    gate/notes prose.  A gated row that names another routine is saying "my
    claim stops where that routine starts"; converting the named routine is
    what lets the gate move."""
    out = []
    for block in _ROW_SPLIT.split(src)[1:]:
        m = _ROW_HEAD.match(block)
        if not m or m.group(2) not in GATED_TIERS:
            continue
        ref = re.search(r'\(some\s+"([^"]+)"\)', block)
        label = f"{m.group(1)}/{ref.group(1) if ref else m.group(2)}"
        out.append((label, block))
    return out


# ---- signal 5: call sites ---------------------------------------------------
# Copied deliberately from scripts/check_routine_liveness.py: the point of that
# list is that a NAME IS NOT A CONTRACT — only emitted instructions count, so
# docstring mentions, `#guard` mentions and label definitions match none of
# them.  Sharing the discipline matters more than sharing the code; if that
# file's list grows, mirror it here.
CALL_PATTERNS = [
    re.compile(r"\bjal\s+(?:ra|x1|x5|t0),\s*([A-Za-z_.][A-Za-z0-9_.]*)"),
    re.compile(r"\bcall\s+([A-Za-z_.][A-Za-z0-9_.]*)"),
    re.compile(r"[;\"]\s*j\s+([A-Za-z_.][A-Za-z0-9_.]*)"),
    re.compile(r"\\n\s*j\s+([A-Za-z_.][A-Za-z0-9_.]*)"),
    re.compile(r"\.jal\s+\.x\d+\s+\"([A-Za-z_.][A-Za-z0-9_.]*)\""),
    re.compile(r"\.la\s+\.x\d+\s+\"([A-Za-z_.][A-Za-z0-9_.]*)\""),
    re.compile(r"\bla\s+[a-z]\d?\d?,\s*([A-Za-z_.][A-Za-z0-9_.]*)"),
    re.compile(r"\b(?:jalOff|laHi|laLo)\s+GuestAddrs\.([A-Za-z_][A-Za-z0-9_]*)"),
]


def count_call_sites(paths, symbols):
    counts = {s: 0 for s in symbols}
    for path in paths:
        txt = read_source(path)
        for pat in CALL_PATTERNS:
            for target in pat.findall(txt):
                if target in counts:
                    counts[target] += 1
    return counts


# ---- authoring shape + derivation edges ------------------------------------
_REPLACE = re.compile(
    r'\.replace\s*\n?\s*"([A-Za-z_.][A-Za-z0-9_.]*)"\s*\n?\s*'
    r'"([A-Za-z_.][A-Za-z0-9_.]*)"')


def authoring_shapes(paths, symbols, all_symbols):
    """symbol -> (shape, detail) and the derivation edges between symbols.

    Shapes, in the order they are tested:
      label-string  an EMITTED label literal `"<sym>:\\n` (or `"<sym>:"`)
                    exists in an EvmAsm Lean file — the routine's text is
                    authored here and is directly transcribable.
      handler-spec  a `label := "<sym>"` field — an `OpcodeHandlerSpec` row
                    whose body is `preBody`/`tail` raw strings; the entry label
                    is emitted by the table renderer, so no label literal
                    exists for it.
      derived       the Function is built by `.replace` from ANOTHER symbol's
                    Function (the witness-codes family).  NOT independently
                    transcribable: converting the base is the prerequisite.
      not-authored  none of the above — the symbol reaches the image some other
                    way (composite emitters, layout templates, data labels).

    This is the representation-independent check the issue asks for in place of
    `GuestAddrs.lean`, which lists String-only routines called by address and
    omits probe-only routines that exist: presence there proves nothing in
    either direction.

    The label regex demands the colon be followed by `\\n` or the closing
    quote, and the enclosing `def` name is recorded.  Both matter: the loose
    form `f'"{sym}:'` matches the roundtrip STUB
    `"witness_codes_lookup_by_hash: ret"` (`Programs/CallFrameRoundtrip.lean`)
    and would report a 620-byte routine as authored-and-ready when what exists
    is a two-token placeholder.  The `def` name in the detail column is what
    lets a reader tell a real emitter from a probe fixture without re-grepping.
    """
    label_lit, handler, derived = {}, {}, {}
    label_pats = {s: re.compile('"' + re.escape(s) + r':(?:\\n|")')
                  for s in symbols}
    handler_pats = {s: re.compile(r'label\s*:=\s*"' + re.escape(s) + '"')
                    for s in symbols}
    for path in paths:
        txt = read_source(path)
        rel = os.path.relpath(path, ROOT)
        for m in _REPLACE.finditer(txt):
            src, dst = m.group(1), m.group(2)
            if src in all_symbols and dst in all_symbols and src != dst:
                derived.setdefault(dst, (src, rel))
        decls = None
        for sym in symbols:
            if sym not in label_lit:
                m = label_pats[sym].search(txt)
                if m:
                    if decls is None:
                        decls = [(d.start(), d.group(1))
                                 for d in _DECL.finditer(txt)]
                    enc = [n for p, n in decls if p < m.start()]
                    label_lit[sym] = f"{rel}:{enc[-1] if enc else '?'}"
            if sym not in handler and handler_pats[sym].search(txt):
                handler[sym] = rel
    shapes = {}
    for sym in symbols:
        if sym in label_lit:
            shapes[sym] = ("label-string", label_lit[sym])
        elif sym in handler:
            shapes[sym] = ("handler-spec", handler[sym])
        elif sym in derived:
            shapes[sym] = ("derived", f"{derived[sym][1]} <- {derived[sym][0]}")
        else:
            shapes[sym] = ("not-authored", "")
    return shapes, derived


# ---- opcode-mnemonic aliases (mechanical) -----------------------------------
_ENTRY = re.compile(r'entry\s+"([A-Z0-9_.]+)"\s+\.(\w+)')
# A blocker naming a tier as a COUNTED SET ("14 `.execSpec` entries have no
# RV64 subroutine"), which is a claim about every member.  Deliberately not a
# bare `` `.conditional` `` search: obligation 3 says "`rlp_item_span` is
# `.conditional` short-list only", which is a claim about ONE ROUTINE, and
# treating it as the opcode set put `h_RETURN`/`h_REVERT`/`h_SELFDESTRUCT` on
# the RLP-decode obligation.
_TIER_SET = re.compile(r"(\d+)\s+`\.(\w+)`\s+(?:entries|rows|opcodes)")
_RANGE = re.compile(r"^([A-Z_]+?)(\d+)\.\.(\d+)$")


def _handler_symbols(mnemonic, symbols):
    """`h_<mnemonic>`, expanding the registry's range form `LOG0..4` into
    `h_LOG0 … h_LOG4`.  Returns only symbols that are actually in the
    unconverted universe."""
    m = _RANGE.match(mnemonic)
    if m:
        stem, lo, hi = m.group(1), int(m.group(2)), int(m.group(3))
        cands = [f"h_{stem}{i}" for i in range(lo, hi + 1)]
    else:
        cands = ["h_" + mnemonic]
    return [c for c in cands if c in symbols]


def opcode_registry(symbols):
    """(mnemonic -> (tier, [handler symbols])) for every opcode registry entry
    with at least one unconverted handler symbol.

    Obligation 5's blockers are opcode-valued (`.opcode "RETURN"`) plus a
    free-text list of the 14 `.execSpec` mnemonics; none of them spells
    `h_RETURN`.  Read from `Progress.lean` rather than hand-listed, so a
    renamed or retired opcode drops out on its own.
    """
    src = read_source(PROGRESS)
    out = {}
    for m in _ENTRY.finditer(src):
        hs = _handler_symbols(m.group(1), symbols)
        if hs:
            out[m.group(1)] = (m.group(2), hs)
    return out


def opcode_context_pattern(mnemonic):
    """Match a mnemonic ONLY where it is being used AS an opcode name.

    A bare `\\bNOT\\b` sweep is not a census, it is a homonym generator: the
    obligation and issue prose is full of emphasis capitals (`does NOT yet
    discharge`, `the CALL family`, `AND`, `OR`, `GAS`, `RETURN`), and an
    earlier revision of this script ranked `h_NOT` eighth on exactly that.
    Three unambiguous contexts, all of which the tree actually uses:
      `MNEMONIC`        backticked, the prose convention for an opcode
      .opcode "MNEMONIC"  the structured `Blocker.opcode` constructor
      h_MNEMONIC        the handler symbol itself
    """
    mn = re.escape(mnemonic)
    return re.compile(r"`" + mn + r"`|\.opcode\s+\"" + mn + r"\"|\bh_" + mn
                      + r"(?![A-Za-z0-9_])")


# ---- issue snapshot ---------------------------------------------------------
def refresh_issues() -> int:
    """The ONE network mode.  Everything else reads the committed snapshot, so
    --write-doc output depends on the tree alone."""
    cmd = ["gh", "issue", "list", "--repo", REPO_SLUG, "--label", "proof",
           "--state", "open", "--json", "number,title,body,url", "--limit", "300"]
    try:
        raw = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError) as exc:
        sys.exit(f"gh issue list failed: {exc}")
    data = json.loads(raw)
    data.sort(key=lambda d: d["number"])
    with open(ISSUES, "w") as f:
        json.dump(data, f, indent=1, sort_keys=True, ensure_ascii=False)
        f.write("\n")
    print(f"wrote {os.path.relpath(ISSUES, ROOT)} ({len(data)} open proof issues)")
    return 0


def load_issues():
    if not os.path.isfile(ISSUES):
        sys.exit(f"missing {os.path.relpath(ISSUES, ROOT)}; create it with\n\n"
                 "    python3 scripts/transcription_queue.py --refresh-issues\n")
    return json.load(open(ISSUES))


# ---- scoring ----------------------------------------------------------------
class Row:
    __slots__ = ("sym", "addr", "size", "shape", "detail", "obligations",
                 "residuals", "issues", "gates", "calls", "via", "base", "src")

    def __init__(self, sym, addr, size):
        self.sym, self.addr, self.size = sym, addr, size
        self.shape, self.detail = "", ""
        self.obligations, self.issues = set(), set()
        self.residuals, self.gates = set(), set()
        self.calls = 0
        self.via = {}     # alias/anchor label -> why (evidence provenance)
        self.base = None  # derived-from symbol that is ITSELF unconverted
        self.src = None   # derived-from symbol, converted or not

    @property
    def score(self):
        return (W_OBLIGATION * len(self.obligations)
                + W_RESIDUAL * len(self.residuals)
                + W_ISSUE * len(self.issues)
                + W_GATE * len(self.gates)
                + W_CALLSITE * min(self.calls, CALLSITE_CAP))

    @property
    def named(self):
        """Does a HUMAN-WRITTEN artifact name this routine as blocking?

        Call sites are a proxy for demand; obligations, residuals, issues and
        gates are somebody actually saying so.  The queue proper is the named
        set; everything whose only signal is popularity is the tail, reported
        as a count rather than pretending to be ranked work.
        """
        return bool(self.obligations or self.residuals or self.issues
                    or self.gates)

    @property
    def cost(self):
        """Extent bytes, or `interior` for a label that shares its address with
        the next symbol.  The guest-image census sizes a symbol as "up to the
        next symbol", which is 0 for an interior label such as
        `.dispatch_loop` (co-located with `.runtime_tx_message_entry`); the
        transcription cost is then the enclosing routine's, not zero."""
        return str(self.size) if self.size else "interior"

    @property
    def evidence(self):
        bits = []
        if self.obligations:
            bits.append("obl " + ",".join(str(o) for o in sorted(self.obligations)))
        if self.residuals:
            bits.append(f"resid {len(self.residuals)}")
        if self.issues:
            bits.append("#" + ",#".join(str(i) for i in sorted(self.issues)))
        if self.gates:
            bits.append(f"gate {len(self.gates)}")
        if self.calls:
            bits.append(f"calls {self.calls}")
        return "; ".join(bits) if bits else "—"


def lean_sources():
    out = []
    for root, _dirs, files in os.walk(EVMASM):
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    out.sort()
    return out


def build_rows():
    universe, converted, n_syms = unconverted_universe()
    symbols = {s for s, _, _ in universe}
    all_symbols = symbols | converted
    paths = lean_sources()

    rows = {s: Row(s, a, b) for s, a, b in universe}
    pats = {s: symbol_pattern(s) for s in symbols}

    # aliases: declared identifier map (spec-side names), then the mechanical
    # opcode-mnemonic map.  alias identifier -> (symbols, why, pattern)
    aliases = {}
    for ident, (sym, why) in IDENT_ALIASES.items():
        if sym in rows:
            aliases[ident] = ([sym], why, symbol_pattern(ident))
    opcodes = opcode_registry(symbols)
    for mn, (_tier, hs) in opcodes.items():
        aliases[mn] = (hs, f"opcode registry mnemonic; guest handler(s) "
                           f"{', '.join('`' + h + '`' for h in hs)}",
                       opcode_context_pattern(mn))
    anchor_pats = [(re.compile(rx), sym, why) for rx, sym, why in PROSE_ANCHORS
                   if sym in rows]
    # Structural tier rule: a blocker that says "the 14 `.execSpec` entries"
    # names a SET, not a symbol.  Expand it from the registry so the set stays
    # correct as opcodes are promoted, instead of transcribing the prose list.
    tier_sets = {}
    for tier in ("execSpec", "conditional", "partly", "notStarted"):
        hs = sorted({h for _mn, (t, hl) in opcodes.items() if t == tier
                     for h in hl})
        if hs:
            tier_sets[tier] = hs

    def credit(text, add, source, tiers=False):
        """Attribute `text` to every symbol it names, directly or via a declared
        alias / opcode context / prose anchor. `add(row)` records the signal."""
        for sym, pat in pats.items():
            if pat.search(text):
                add(rows[sym])
        for ident, (syms, why, pat) in aliases.items():
            if pat.search(text):
                for sym in syms:
                    add(rows[sym])
                    rows[sym].via[f"alias `{ident}` ({source})"] = why
        for pat, sym, why in anchor_pats:
            if pat.search(text):
                add(rows[sym])
                rows[sym].via[f"anchor `{pat.pattern}` ({source})"] = why
        if tiers:
            for count, tier in _TIER_SET.findall(text):
                for sym in tier_sets.get(tier, ()):
                    add(rows[sym])
                    rows[sym].via[f"tier set `.{tier}` ({source})"] = (
                        f"the blocker counts \"{count} `.{tier}` entries\" — a "
                        f"SET, not a symbol; expanded from `Progress.lean`'s "
                        f"registry so it tracks promotions")

    # 1. obligations
    for oid, text in obligation_blocker_texts(
            read_source(OBLIGATIONS)):
        credit(text, lambda r, o=oid: r.obligations.add(o), f"obligation {oid}",
               tiers=True)

    # 2. residuals
    resid_decls = residual_blocks(paths)
    for label, text in resid_decls:
        credit(text, lambda r, l=label: r.residuals.add(l), "residual")

    # 3. issues (snapshot; SELF_ISSUE excluded — see its comment)
    for it in load_issues():
        num = it["number"]
        if num == SELF_ISSUE:
            continue
        text = (it.get("title") or "") + "\n" + (it.get("body") or "")
        credit(text, lambda r, n=num: r.issues.add(n), f"#{num}")

    # 4. registry gates
    for label, text in registry_gate_blocks(
            read_source(ROUTINES)):
        credit(text, lambda r, l=label: r.gates.add(l), "registry")

    # 5. call sites
    for sym, n in count_call_sites(paths, symbols).items():
        rows[sym].calls = n

    # authoring shape + derivation roll-up
    shapes, derived = authoring_shapes(paths, symbols, all_symbols)
    for sym, (shape, detail) in shapes.items():
        rows[sym].shape, rows[sym].detail = shape, detail
    for dst, (src, _rel) in sorted(derived.items()):
        if dst in rows:
            rows[dst].src = src
        if dst in rows and src in rows:
            rows[dst].base = src
            # A `.replace`-derived Function cannot be transcribed on its own,
            # so everything waiting on it is really waiting on the base.
            base = rows[src]
            base.obligations |= rows[dst].obligations
            base.issues |= rows[dst].issues
            base.residuals |= rows[dst].residuals
            base.gates |= rows[dst].gates
            base.via[f"rolled up from `{dst}`"] = (
                f"`{dst}` is built by `.replace` from `{src}`; the base must be "
                "transcribed first")

    # A `.replace`-derived row must never rank ABOVE the base it cannot be
    # written without, so it sorts on the base's score and loses every tie.
    def key(r):
        eff = rows[r.base].score if r.base else r.score
        return (-eff, r.base is not None, -r.score, r.size, r.sym)

    ordered = sorted(rows.values(), key=key)
    return ordered, converted, n_syms, anchor_pats, len(resid_decls)


# ---- rendering ---------------------------------------------------------------
def queue_table(rows):
    out = ["| # | symbol | demand | evidence | shape | cost (B) |",
           "|---:|---|---:|---|---|---:|"]
    for i, r in enumerate(rows, 1):
        shape = r.shape
        if r.base:
            shape += f" (base `{r.base}`)"
        elif r.src:
            shape += f" (from converted `{r.src}`)"
        out.append(f"| {i} | `{r.sym}` | {r.score} | {r.evidence} | {shape} "
                   f"| {r.cost} |")
    return "\n".join(out)


def tail_table(rows):
    out = ["| symbol | call sites | shape | cost (B) |", "|---|---:|---|---:|"]
    for r in rows:
        out.append(f"| `{r.sym}` | {r.calls} | {r.shape} | {r.cost} |")
    return "\n".join(out)


def render_doc(rows, converted, n_syms, anchors, top, tail_top,
               n_resid_decls):
    named = [r for r in rows if r.named]
    tail = sorted((r for r in rows if not r.named and r.calls),
                  key=lambda r: (-r.calls, r.size, r.sym))
    silent = [r for r in rows if not r.named and not r.calls]
    by_shape = {}
    for r in rows:
        by_shape[r.shape] = by_shape.get(r.shape, 0) + 1
    alias_rows = "\n".join(
        f"| `{ident}` | `{sym}` | {why} |"
        for ident, (sym, why) in sorted(IDENT_ALIASES.items()))
    anchor_rows = "\n".join(
        f"| `{pat.pattern}` | `{sym}` | {why} |" for pat, sym, why in anchors)
    via_rows = "\n".join(
        f"| `{r.sym}` | {k} | {v} |"
        for r in named for k, v in sorted(r.via.items()))
    shape_rows = "\n".join(
        f"| `{k}` | {by_shape[k]} |" for k in sorted(by_shape))
    subst = {
        "N_SYMS": str(n_syms),
        "N_CONVERTED": str(n_syms - len(rows)),
        "N_MANIFEST": str(len(converted)),
        "N_UNLINKED": str(len(converted) - (n_syms - len(rows))),
        "N_UNCONVERTED": str(len(rows)),
        "N_NAMED": str(len(named)),
        "N_TAIL": str(len(tail)),
        "N_SILENT": str(len(silent)),
        "TOP_N": str(min(top, len(named))),
        "TAIL_TOP_N": str(min(tail_top, len(tail))),
        "TOTAL_UNCONVERTED_BYTES": str(sum(r.size for r in rows)),
        "NAMED_BYTES": str(sum(r.size for r in named)),
        "W_OBLIGATION": str(W_OBLIGATION),
        "W_RESIDUAL": str(W_RESIDUAL),
        "W_ISSUE": str(W_ISSUE),
        "W_GATE": str(W_GATE),
        "W_CALLSITE": str(W_CALLSITE),
        "CALLSITE_CAP": str(CALLSITE_CAP),
        "CALLSITE_MAX": str(W_CALLSITE * CALLSITE_CAP),
        "SELF_ISSUE": str(SELF_ISSUE),
        "N_ISSUES": str(len(load_issues())),
        "N_RESIDUAL_DECLS": str(n_resid_decls),
        "N_RESIDUAL_HITS": str(sum(1 for r in rows if r.residuals)),
        "QUEUE_TABLE": queue_table(named[:top]),
        "FULL_TABLE": queue_table(named),
        "TAIL_TABLE": tail_table(tail[:tail_top]),
        "ALIAS_TABLE": alias_rows,
        "ANCHOR_TABLE": anchor_rows,
        "VIA_TABLE": via_rows,
        "SHAPE_TABLE": shape_rows,
    }
    doc = open(TEMPLATE, encoding="utf-8").read()
    for key, val in subst.items():
        doc = doc.replace(f"@@{key}@@", val)
    leftover = sorted(set(re.findall(r"@@[A-Z_0-9]+@@", doc)))
    if leftover:
        sys.exit(f"template slots left unfilled: {leftover} — "
                 "template/generator drift, refusing to emit")
    return doc


# ---- self-test ---------------------------------------------------------------
def run_self_test() -> int:
    problems = []

    def check(cond, msg):
        if not cond:
            problems.append(msg)

    # 1. Boundary matching: sibling symbols must not bleed into each other.
    p = symbol_pattern("witness_lookup_by_hash")
    check(p.search("residual `witness_lookup_by_hash` triple"),
          "bare mention must match")
    check(not p.search("GuestAddrs.witness_lookup_by_hash_indexed"),
          "must NOT match the distinct _indexed symbol")
    d = symbol_pattern("dispatch_loop")
    check(not d.search("j .dispatch_loop"),
          "`dispatch_loop` must not match the dotted label (separate census row)")
    check(symbol_pattern(".dispatch_loop").search("  j .dispatch_loop\\n"),
          "dotted label must match itself")

    # 2. Obligation parse: blockedBy only, note excluded (a `note` naming a
    #    now-.proven routine is the OPPOSITE of a blocking claim).
    synthetic = (
        "def obligations : List Obligation := [\n"
        "  { id := 7, name := \"x\",\n"
        "    status := .blocked,\n"
        "    blockedBy := [.infra \"needs alpha_routine\"],\n"
        "    auditedAt := some \"d\",\n"
        "    note := \"beta_routine is now .proven\" },\n"
        "  { id := 10, name := \"y\",\n"
        "    status := .blocked,\n"
        "    blockedBy := [.infra \"needs alpha_routine too\"],\n"
        "    note := \"gamma_routine\" },\n]")
    parsed = obligation_blocker_texts(synthetic)
    check([o for o, _ in parsed] == [7, 10], f"obligation ids {parsed}")
    joined = " ".join(t for _, t in parsed)
    check("alpha_routine" in joined, "blocker text not captured")
    check("beta_routine" not in joined, "note text leaked into blocker region")
    check("gamma_routine" not in joined,
          "note text leaked (no auditedAt variant)")

    # 3. Weight ordering is the whole ranking claim: one obligation row must
    #    outrank ANY amount of call-site popularity.
    check(W_CALLSITE * CALLSITE_CAP < W_OBLIGATION,
          "call-site cap can outrank an obligation row — demand/cost inverted")
    a, b = Row("a", 0, 10), Row("b", 0, 10)
    a.obligations = {7}
    b.calls = 10_000
    check(b.score == W_CALLSITE * CALLSITE_CAP, "call-site cap does not bind")
    check(a.score > b.score, "a blocking symbol must outrank a popular one")
    big, small = Row("big", 0, 40_000), Row("small", 0, 8)
    big.obligations = {7}
    check(big.score > small.score, "byte size must not enter the score")

    # 4. Derivation regex must see the witness-codes `.replace` chain shape.
    m = _REPLACE.search('(f.replace\n      "witness_index_build"\n'
                        '      "witness_codes_index_build")')
    check(m and m.group(1) == "witness_index_build"
          and m.group(2) == "witness_codes_index_build",
          "`.replace` derivation shape not recognised")

    # 5. Registry gate parse keeps only gated tiers.
    gated = registry_gate_blocks(
        '  routine "p" .proven (some "p_spec")\n      (notes := "names q_r"),\n'
        '  routine "c" .conditional (some "c_spec")\n      (gate := "needs z_r"),\n')
    check([g[0] for g in gated] == ["c/c_spec"], f"gate rows {gated}")

    if problems:
        for msg in problems:
            print(f"SELF-TEST FAIL: {msg}")
        return 1
    print("self-test PASS: symbol boundaries, blockedBy-only obligation parse, "
          "demand-over-cost weight ordering, `.replace` derivation shape, "
          "gated-tier row filter.")
    return 0


# ---- main --------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description="demand-first transcription queue")
    ap.add_argument("--top", type=int, default=25, help="rows to print (default 25)")
    ap.add_argument("--all", action="store_true", help="print every scored row")
    ap.add_argument("--md", action="store_true", help="markdown tables to stdout")
    ap.add_argument("--write-doc", action="store_true",
                    help=f"regenerate {os.path.relpath(DOC, ROOT)}")
    ap.add_argument("--check-doc", action="store_true",
                    help="exit 1 if the committed doc differs from --write-doc")
    ap.add_argument("--refresh-issues", action="store_true",
                    help="ONLY network mode: refresh the proof-issue snapshot")
    ap.add_argument("--self-test", action="store_true",
                    help="run the scorer/matcher self-test and exit")
    args = ap.parse_args()

    if args.self_test:
        return run_self_test()
    if args.refresh_issues:
        return refresh_issues()

    rows, converted, n_syms, anchors, n_resid = build_rows()
    named = [r for r in rows if r.named]
    doc_top = len(named) if args.all else args.top

    if args.write_doc or args.check_doc:
        doc = render_doc(rows, converted, n_syms, anchors, DOC_TOP,
                         DOC_TAIL_TOP, n_resid)
        rel = os.path.relpath(DOC, ROOT)
        if args.write_doc:
            with open(DOC, "w") as f:
                f.write(doc)
            print(f"wrote {rel}")
            return 0
        if not os.path.isfile(DOC):
            sys.exit(f"{rel} missing; regenerate:\n\n"
                     "    python3 scripts/transcription_queue.py --write-doc\n")
        current = open(DOC).read()
        if current != doc:
            sys.stdout.writelines(difflib.unified_diff(
                current.splitlines(keepends=True), doc.splitlines(keepends=True),
                fromfile="committed", tofile="regenerated"))
            sys.exit(f"\n{rel} is out of date relative to the live generator. "
                     "Regenerate:\n\n"
                     "    python3 scripts/transcription_queue.py --write-doc\n")
        print(f"{rel}: CLEAN")
        return 0

    if args.md:
        print(queue_table(named[:doc_top]))
        return 0

    tail = [r for r in rows if not r.named and r.calls]
    print(f"guest `.text` symbols: {n_syms}  converted+linked: "
          f"{n_syms - len(rows)}  unconverted: {len(rows)}  "
          f"(manifest total {len(converted)}, "
          f"{len(converted) - (n_syms - len(rows))} converted-but-not-linked)")
    print(f"named as blocking by an obligation / residual / issue / gate: "
          f"{len(named)}")
    print(f"call-sites-only tail: {len(tail)}   no signal at all: "
          f"{len(rows) - len(named) - len(tail)}")
    print(f"cost of the named set: {sum(r.size for r in named)} B of "
          f"{sum(r.size for r in rows)} B unconverted\n")
    print(f"{'#':>3}  {'symbol':<40} {'demand':>6}  {'cost B':>8}  "
          f"{'shape':<13}  evidence")
    for i, r in enumerate(named[:doc_top], 1):
        print(f"{i:>3}  {r.sym:<40} {r.score:>6}  {r.cost:>8}  "
              f"{r.shape:<13}  {r.evidence}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
