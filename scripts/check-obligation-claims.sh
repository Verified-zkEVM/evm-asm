#!/usr/bin/env bash
#
# check-obligation-claims.sh — architecture fitness function for the three
# staleness classes that `no_proven_opcode_blockers` and
# `check-obligation-blockers.sh` between them do NOT cover (#12129).
#
# Why a sibling and not an extension of check-obligation-blockers.sh
# -----------------------------------------------------------------
# That script needs network + `gh` auth (it asks GitHub whether a cited issue is
# closed), so it must skip itself whenever either is missing — which is most CI
# jobs. Every check here is LOCAL and deterministic: tree contents, file text,
# and a generated report. Keeping them apart means these can eventually run
# `--strict` in CI without dragging a network dependency along.
#
# The three classes
# -----------------
#   A. An `infra` blocker asserting a declaration is MISSING when that exact
#      declaration EXISTS in the tree. The claim is then provably false, and it
#      is the expensive kind of wrong: agents triage from these rows, so a
#      false "blocked on X" makes startable work look unstartable. #12129 was
#      filed because obligations 7 and 10 claimed `witness_lookup_by_hash` was
#      unconverted months after `witnessLookupByHash_prog` landed.
#
#   B. Registry counts embedded as literals in obligation prose — ALREADY
#      COVERED by `scripts/check-embedded-counts.sh` (same pattern, same file,
#      also filed under #12129). Not reimplemented here; see the note at its
#      former position below.
#
#   C. A `.text` coverage percentage hand-written into PLAN.md or into
#      EvmAsm/Progress/Obligations.lean. That number is GENERATED into
#      docs/4ch8f-guest-image-coverage.md by scripts/guest_image_coverage.py and
#      moves every time a `_prog` lands. PLAN.md carried "~24.65%" when the
#      generated value had reached 35.36% — stale by more than ten points — and
#      obligation 8's blocker cell quoted "121500 of 343356 bytes" against an
#      actual 121600 of 343576, i.e. two of its three literals wrong, directly
#      under its own "re-measure before citing" caveat. A number that can be
#      generated must not be hand-maintained.
#
# ⚠️ Class A is deliberately NARROW, and the broad version #12129 asked for was
# tried first and REJECTED as unsound. Recorded here so nobody re-widens it.
#
# The ask was: "flag any `infra` blocker naming a `_prog`/`_spec_within`
# identifier that exists in the tree". Implemented literally, that produced FIVE
# findings on the live tree, and all five were false positives, because a
# well-maintained blocker cell names existing declarations precisely in order to
# say what is NOT blocking:
#
#   obligation 3: "⭐ TRANSCRIPTION NO LONGER BLOCKS THIS — both programs landed
#                  … `rlpWalkNextShared_prog` … and `rlpValidatePayload_prog`"
#   obligation 4: "Representation is NOT the blocker — `zkvmSha256_prog` exists"
#
# Flagging those would punish exactly the maintenance the gate is meant to
# encourage. It is the same noise class the sibling script documents for issue
# citations ("the `note` prose legitimately cites closed issues as evidence"),
# one level deeper — and it is why obligation rows carry `auditedAt` instead of
# being fully mechanised.
#
# A related trap in the same area: matching declaration names as SUBSTRINGS. The
# live obligation-7/10 blocker names `witness_lookup_by_hash_spec_within`, which
# does NOT exist — what exist are the domain-restricted
# `..._spec_within_empty_section` and `..._spec_within_enabled_empty`. A
# substring grep matches those and flags an honest blocker whose whole point is
# that the GENERAL/HIT-domain theorem is absent.
#
# So class A checks the ONE claim shape that is genuinely falsifiable: an
# assertion that a guest symbol is UNCONVERTED / untranscribed, when
# `GuestImageEntries.lean` shows a `_prog` for it. That is exactly the bug that
# motivated #12129 (obligations 7 and 10 called `witness_lookup_by_hash` "620 B
# UNCONVERTED" months after `witnessLookupByHash_prog` landed), and
# `GuestImageEntries.lean` is the authority on what the deployed image contains.
# An absence phrase and the symbol must occur in the SAME SENTENCE, so a cell
# that merely mentions a converted symbol elsewhere is untouched.
#
# Known limitation, accepted deliberately: obligation cells contain very long
# run-on sentences, and within one such sentence every converted symbol is
# reported, not just the one the absence phrase is about. Reproducing #12129's
# historical text confirmed the intended target (`witness_lookup_by_hash`) fires,
# alongside two other converted symbols in the same clause. That is why findings
# NAME the symbol and the triggering phrase and why the default is advisory: a
# human adjudicates, and the remedy in every case is to narrow the claim to the
# domain that is genuinely missing.
#
# Usage:
#   scripts/check-obligation-claims.sh          # advisory (always exit 0)
#   scripts/check-obligation-claims.sh --strict
#   scripts/check-obligation-claims.sh --self-test  # class-A controls, both directions # exit 1 on any finding
#
set -uo pipefail
cd "$(dirname "$0")/.."

STRICT=0
[[ "${1:-}" == "--strict" ]] && STRICT=1

# ---------------------------------------------------------------------------
# --self-test — controls for class A, in BOTH directions.
# ---------------------------------------------------------------------------
# Why this exists: until now this gate had no controls, and it reports OK on the
# current tree — so "it passes" was equally consistent with "the phrase list
# still works" and "the phrase list matches nothing any more". The class-A regex
# is deliberately narrow (a bare `TRANSCRIPTION` must NOT count, because
# obligation 3 says "TRANSCRIPTION NO LONGER BLOCKS THIS"), and narrowness is
# exactly the property that rots silently when someone edits the alternation.
#
# Runs the REAL logic against fixtures via the two env overrides above, so the
# controls exercise the shipped code path rather than a copy of it.
if [[ "${1:-}" == "--self-test" ]]; then
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  fails=0

  # A converted symbol, in the shape class A reads GuestImageEntries in.
  cat >"$tmp/entries.lean" <<'FIXEOF'
  (GuestAddrs.witness_lookup_by_hash, witnessLookupByHash_prog),
  (GuestAddrs.rlp_walk_next_shared, rlpWalkNextShared_prog),
FIXEOF

  emit_progress() {   # $1 = the "Blocked by" cell text
    { echo '| # | Obligation | Status | Blocked by | Audited |'
      echo '|---|---|---|---|---|'
      echo "| 7 | probe | open | $1 | - |"
      echo ''
    } >"$tmp/progress.md"
  }

  run_a() {
    OBLIGATION_CLAIMS_PROGRESS="$tmp/progress.md" \
    OBLIGATION_CLAIMS_ENTRIES="$tmp/entries.lean" \
    bash "$0" 2>&1 | grep -c 'IS converted' || true
  }

  # (1) POSITIVE controls — ONE PER PHRASE, deliberately not a single fixture
  #     containing several of them.
  #     Keep each fixture free of the other absence phrases: in particular,
  #     the TRANSCRIPTION-first fixture must not also say "blocked on
  #     transcription", or deleting this alternative would go unnoticed.
  #
  #     ⚠️ This was originally one fixture reading "620 B UNCONVERTED
  #     `witness_lookup_by_hash` — Blocked on TRANSCRIPTION first", and a mutation
  #     test exposed it as too weak: deleting `UNCONVERTED` from the alternation
  #     still left `TRANSCRIPTION first` matching the same fixture, so the control
  #     passed while the phrase list had genuinely lost a case. Testing the
  #     DISJUNCTION only proves some phrase survives, not that each does.
  while IFS='|' read -r label cell; do
    [[ -z "$label" ]] && continue
    emit_progress "$cell"
    if [[ "$(run_a)" == "0" ]]; then
      echo "check-obligation-claims --self-test: FAIL — absence phrase '${label}' no longer trips class A (fixture: ${cell})" >&2
      echo "  Each phrase in the ABSENT alternation must be independently detected; a" >&2
      echo "  deleted case is how #12129's motivating bug would come back unnoticed." >&2
      fails=1
    fi
  done <<'CASES'
UNCONVERTED|620 B UNCONVERTED `witness_lookup_by_hash`, still pending.
TRANSCRIPTION first|`witness_lookup_by_hash` — TRANSCRIPTION first is the remaining blocker.
untranscribed|the `witness_lookup_by_hash` body is untranscribed.
needs transcription|`witness_lookup_by_hash` needs transcription before a triple.
blocked on transcription|blocked on transcription of `witness_lookup_by_hash`.
not yet converted|`witness_lookup_by_hash` is not yet converted.
CASES

  # (2) NEGATIVE control — a RETRACTED claim must not trip. This is real
  #     obligation-3 text; a bare `TRANSCRIPTION` in the alternation would break it.
  emit_progress 'TRANSCRIPTION NO LONGER BLOCKS THIS — both programs landed: `rlp_walk_next_shared` is converted.'
  if [[ "$(run_a)" != "0" ]]; then
    echo "check-obligation-claims --self-test: FAIL — a RETRACTED claim was flagged; the phrase list has been widened too far (a bare TRANSCRIPTION must not count)" >&2
    fails=1
  fi

  # (3) NEGATIVE control — sentence scoping. An absence phrase about an
  #     unconverted thing must not implicate a converted symbol in the NEXT
  #     sentence. This is the ±140-char window bug the header describes.
  emit_progress 'the loop is inside the untranscribed dispatcher. Separately `witness_lookup_by_hash` has no machine post yet.'
  if [[ "$(run_a)" != "0" ]]; then
    echo "check-obligation-claims --self-test: FAIL — sentence scoping regressed: an absence phrase implicated a converted symbol in a LATER sentence" >&2
    fails=1
  fi

  # (4) NEGATIVE control — a genuine absence claim about a genuinely
  #     unconverted symbol must stay silent.
  emit_progress 'UNCONVERTED `totally_bogus_symbol` — blocked on transcription first'
  if [[ "$(run_a)" != "0" ]]; then
    echo "check-obligation-claims --self-test: FAIL — flagged a symbol that is NOT in GuestImageEntries" >&2
    fails=1
  fi

  if (( fails )); then exit 1; fi
  echo "check-obligation-claims --self-test: OK — class A trips on the #12129 text; a retracted claim, a later-sentence mention, and an unconverted symbol do not."
  exit 0
fi

# Preflight. A gate that quietly skips itself is worse than no gate — it reports
# OK forever and nobody notices the class stopped being checked. Every tool used
# below is POSIX-standard, so a miss here means a genuinely broken environment
# and is reported as a hard error rather than a skip.
for tool in grep awk python3 cut head sort; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "check-obligation-claims: FATAL — required tool \`$tool\` not on PATH." >&2
    echo "  Refusing to report OK on unchecked classes." >&2
    exit 1
  fi
done

# Class A's two inputs are overridable ONLY so `--self-test` can point the real
# logic at fixtures (see the self-test block at the end). Production runs use the
# defaults; nothing else sets these.
# DRIFT.md, not PROGRESS.md: the latter stopped being committed in #12683, and
# DRIFT.md carries the SAME rendered obligation table (both are
# `renderObligations` in MainProgress.lean) while remaining committed and
# drift-gated by check-drift.sh. So class A keeps its "only trips once the
# blocker is visible on the dashboard" property and still needs no Lean build.
PROGRESS="${OBLIGATION_CLAIMS_PROGRESS:-DRIFT.md}"
ENTRIES="${OBLIGATION_CLAIMS_ENTRIES:-EvmAsm/Codegen/Proofs/GuestImageEntries.lean}"
OBLIGATIONS="EvmAsm/Progress/Obligations.lean"
PLAN="PLAN.md"
COVERAGE_DOC="docs/4ch8f-guest-image-coverage.md"
ROOT_PINS="EvmAsm/Codegen/RegionMapLinkPins.lean"

findings=0

# ---------------------------------------------------------------------------
# Class A — an infra blocker naming a declaration that exists.
# ---------------------------------------------------------------------------
# Parsed from the RENDERED table in DRIFT.md rather than the Lean source, for
# the same reason as the sibling script: the rendered "Blocked by" cell is
# exactly the blocker text, pipe-delimited, one obligation per line, with none of
# the `\`-continuation splicing that Lean string literals use. It also means a
# blocker only trips this check once it is visible on the dashboard.
if [[ -f "$PROGRESS" && -f "$ENTRIES" ]]; then
  a_out="$(python3 - "$PROGRESS" "$ENTRIES" <<'PYEOF'
import re, sys

progress, entries = sys.argv[1], sys.argv[2]

# The set of guest symbols that ARE converted: exactly the left-hand side of the
# (GuestAddrs.<sym>, <sym>_prog) pairs in GuestImageEntries.lean. That file is the
# authority on what the deployed image contains, so "symbol X is unconverted" is
# provably false iff X appears here.
converted = set(re.findall(r'GuestAddrs\.([a-z][a-z0-9_]*)\s*,', open(entries).read()))

# Phrases that ASSERT ABSENCE. Only these turn a symbol mention into a checkable
# claim; see the header note on why a bare mention must not be flagged.
ABSENT = re.compile(
    # re.I makes a separate lowercase `unconverted` alternative redundant.
    r'UNCONVERTED|untranscribed|NOT[ _]CONVERTED'
    r'|needs? transcription|blocked on transcription|awaiting transcription'
    r'|TRANSCRIPTION first|not yet converted|no `?\w+_prog`? exists',
    re.I)

rows, intable = [], False
for line in open(progress):
    if line.startswith('| # | Obligation | Status | Blocked by |'):
        intable = True
        continue
    if intable and re.match(r'^\|\s*\d+\s*\|', line):
        f = line.split('|')
        if len(f) > 5:
            rows.append((f[1].strip(), f[4].strip()))
        continue
    if intable and not line.startswith('|'):
        intable = False

# Scope each absence phrase to its own SENTENCE, not a character window.
#
# A ±140-char window was tried and over-triggered: obligation 4 contains
# "... is simply inside the untranscribed dispatcher. Ranked in
# `docs/4ch8f-transcription-queue.md`, `stage_system_call` has no machine post
# yet, and the `execution_requests_hash` hash-half compose is still open."
# The absence claim was about the DISPATCHER; the two converted symbols in the
# NEXT sentence carry entirely different claims ("no machine post yet", "compose
# still open").
#
# ⚠️ The dispatcher half of that example is now HISTORICAL: #12204 step 3 landed
# `dispatchLoop_prog`, and obligation 4's text was corrected to say so. The
# sentence-scoping rule this comment justifies is unaffected — it is about the
# WINDOW, not about which claim happened to be true. Kept as the worked example
# because no shorter one exercises the boundary.
# A window bled across the sentence boundary and reported both as stale.
for oid, cell in rows:
    for sentence in re.split(r'(?<=[.;])\s+', cell):
        m = ABSENT.search(sentence)
        if not m:
            continue
        for sym in set(re.findall(r'\b([a-z][a-z0-9]*(?:_[a-z0-9]+){1,})\b', sentence)):
            if sym in converted:
                print(f'{oid}\t{sym}\t{m.group(0)}')
PYEOF
)" || a_out=""

  while IFS=$'\t' read -r oid sym phrase; do
    [[ -z "$oid" ]] && continue
    echo "  ✗  obligation $oid says \"$phrase\" near \`$sym\`, but that symbol IS converted"
    echo "       (it has a _prog entry in $ENTRIES)"
    findings=$((findings + 1))
  done <<<"$a_out"
else
  # A skip here is not benign: class A is the #12129 gate, and "input missing"
  # is indistinguishable from "nothing to report" in the exit code. Both inputs
  # are committed files, so this can only mean the tree is broken or a path was
  # renamed out from under this script — fail the gate in strict mode rather
  # than reporting OK on an unchecked class (same stance as the tool check).
  echo "check-obligation-claims: $PROGRESS or $ENTRIES missing — class A NOT checked." >&2
  if (( STRICT )); then
    echo "  Refusing to pass --strict with class A unchecked." >&2
    exit 1
  fi
fi

# ---------------------------------------------------------------------------
# Class B — NOT implemented here: `scripts/check-embedded-counts.sh` already
# covers it, with the identical pattern `[0-9]+ (rows|proven|conditional|partly)`
# over the same file, and is itself attributed to #12129. Duplicating it would
# just mean two gates to keep in sync. Run both; this one deliberately has no
# class-B branch.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Class C — a hand-written coverage percentage in prose.
# ---------------------------------------------------------------------------
# Scanned in BOTH PLAN.md and EvmAsm/Progress/Obligations.lean. Restricting this
# to PLAN.md was a real gap: obligation 8's coverage blocker quoted
# "35.39% of `.text` (121500 of 343356 bytes)" while the generated doc said
# 121600 of 343576 — two of the three literals stale, under a caveat reading
# "re-measure before citing" that had plainly not been followed. Obligations.lean
# is the WORSE place for a stale figure than PLAN.md, because those rows render
# into the rendered dashboard and are what other agents triage from.
c_out="$(python3 - "$PLAN" "$OBLIGATIONS" <<'PYEOF'
import re, sys, os

# A LOGICAL line is a finding when it carries a decimal percentage AND the word
# "coverage" AND mentions `.text` — three INDEPENDENT conditions.
#
# ⚠️ Do NOT try to match the phrase "`.text` coverage" as contiguous text. The
# real instances have three different word orders — "~24.65% `.text` coverage",
# "23.76% of `.text`", and "pins 35.39% \\\n of `.text`" — with markdown
# backticks and, in the Lean file, a string-literal line continuation in
# between. An earlier version anchored on `\.text coverage` and silently matched
# NONE of them; a negative control (reintroduce the stale figure, confirm the
# gate fires) is what caught it.
#
# ⚠️ Physical-line grepping is ALSO not enough, and that was the second bug here.
# In Obligations.lean the percentage and "of `.text`" straddle a `\`
# continuation, so no single physical line satisfies all three conditions and a
# per-line scan reports OK on a file that is stale. Splice continuations into a
# logical line first, and report the FIRST physical line number of that logical
# line — which is where the edit goes.
PCT = re.compile(r'[0-9]+\.[0-9]+\s*%')

def logical_lines(path):
    """Yield (first_physical_lineno, spliced_text). A trailing backslash — Lean's
    string-literal continuation — joins to the next line. Markdown has none, so
    for .md files this degenerates to one logical line per physical line."""
    with open(path, encoding='utf-8') as fh:
        raw = fh.read().split('\n')
    i = 0
    while i < len(raw):
        start = i + 1
        buf = raw[i]
        while buf.rstrip().endswith('\\') and i + 1 < len(raw):
            buf = buf.rstrip()[:-1] + ' ' + raw[i + 1]
            i += 1
        yield start, buf
        i += 1

hits = []
for path in sys.argv[1:]:
    if not os.path.isfile(path):
        continue
    for lineno, text in logical_lines(path):
        if not PCT.search(text):
            continue
        if 'coverage' not in text.lower():
            continue
        if '.text' not in text:
            continue
        # Collapse whitespace so a spliced multi-line literal prints readably.
        hits.append((path, lineno, ' '.join(text.split())[:160]))

for path, lineno, text in hits:
    print(f'{path}\t{lineno}\t{text}')
PYEOF
)" || { echo "check-obligation-claims: FATAL — class C scanner failed." >&2; exit 1; }

while IFS=$'\t' read -r c_file c_line c_text; do
  [[ -z "$c_file" ]] && continue
  echo "  ✗  $c_file:$c_line hand-writes a .text coverage percentage:"
  echo "       $c_text"
  echo "       that number is generated into $COVERAGE_DOC by scripts/guest_image_coverage.py"
  findings=$((findings + 1))
done <<< "$c_out"

# ---------------------------------------------------------------------------
# Class D — prose that CITES `textSizeBytes` must quote its real value.
# ---------------------------------------------------------------------------
# This is the sharpest member of the family, because unlike class C it is checked
# against a Lean constant rather than a generated report: `.text`'s size is
# `RegionMapLinkPins.textSizeBytes`, one `abbrev`, and any prose that names that
# constant and then writes a byte count or an extent is making a claim that is
# mechanically TRUE or FALSE.
#
# It found a live instance the moment it was written. `GuestImage.lean`'s
# `guestImageCodeReq` doc block read:
#
#   `.text` `[0x80000000, 0x80053d3c)` = 343356 bytes
#   (`RegionMapLinkPins.textSizeBytes` `0x53d3c`)
#
# against an actual `0x53e18` = 343576 — all THREE literals wrong, under a caveat
# that opens "measure; do not copy older prose". That is the same failure as
# obligation 8's cell and PLAN.md's percentage: the warning not to copy stale
# figures does not stop figures going stale, because nothing checks them.
d_out="$(python3 - "$ROOT_PINS" <<'PYEOF'
import re, subprocess, sys

pins = sys.argv[1]
m = re.search(r'abbrev\s+textSizeBytes\s*:\s*Nat\s*:=\s*(0x[0-9a-fA-F]+|\d+)',
              open(pins, encoding='utf-8').read())
if not m:
    print('FATAL\t0\tcould not read textSizeBytes from ' + pins)
    sys.exit(0)
V = int(m.group(1), 0)
TEXT_BASE = 0x80000000
END = TEXT_BASE + V

# Only files that NAME the constant are scanned; a byte count elsewhere is not a
# claim about it. Tracked files only, so vendored/build output stays out.
files = subprocess.run(['git', 'ls-files', '*.lean', '*.md'],
                       capture_output=True, text=True, check=True).stdout.split()

# Both patterns are ANCHORED on syntax that can only be a `.text` extent claim.
#
# ⚠️ A third rule was tried and REMOVED as unsound: "any bare 5-hex-digit literal
# in a paragraph that mentions textSizeBytes". It produced FIVE findings and all
# five were false positives — `docs/evm-memory-pool-plan.md:194`'s `0x39000` is a
# `LUI` immediate (`25<<12`), and PLAN.md's `0x61408`/`0x59bf8` are unrelated
# region-map values that landed in the same "paragraph" only because markdown
# bullet lists have no blank lines between items, so the paragraph unit
# over-merged. Same failure mode as the broad class-A rule this script also
# documents rejecting: proximity to a constant's NAME is not a claim about its
# VALUE. Do not re-add it — require the anchor.
RANGE = re.compile(r'\[\s*0x80000000\s*,\s*(0x[0-9a-fA-F]{8})\s*\)')
# The "extent equals" idiom, `= 343356 bytes`. The `=` is load-bearing: a byte
# count without it is usually some other measurement in the same block.
BYTES = re.compile(r'=\s*(\d{5,7})\s*(?:B\b|bytes)')

for path in files:
    try:
        raw = open(path, encoding='utf-8').read().split('\n')
    except (OSError, UnicodeDecodeError):
        continue
    if not any('textSizeBytes' in l for l in raw):
        continue
    # A PARAGRAPH is the claim unit: the constant and the figures it governs are
    # usually on different lines of one doc comment / markdown block. Blank lines
    # and the `-/` doc-comment terminator end a paragraph.
    para, start = [], 1
    def flush(para, start):
        text = ' '.join(para)
        if 'textSizeBytes' not in text:
            return
        for hx in RANGE.findall(text):
            if int(hx, 16) != END:
                yield (start, f'cites textSizeBytes and writes `.text` end {hx}, '
                              f'but 0x80000000 + 0x{V:x} = 0x{END:x}')
        for dec in BYTES.findall(text):
            if int(dec) != V:
                yield (start, f'cites textSizeBytes and writes = {dec} bytes, '
                              f'but textSizeBytes = {V}')
    for i, line in enumerate(raw, 1):
        if not para:
            start = i
        stripped = line.strip()
        if stripped == '' or stripped.endswith('-/'):
            if stripped.endswith('-/'):
                para.append(line)
            for lineno, msg in flush(para, start):
                print(f'{path}\t{lineno}\t{msg}')
            para = []
            continue
        para.append(line)
    for lineno, msg in flush(para, start):
        print(f'{path}\t{lineno}\t{msg}')
PYEOF
)" || { echo "check-obligation-claims: FATAL — class D scanner failed." >&2; exit 1; }

while IFS=$'\t' read -r d_file d_line d_text; do
  [[ -z "$d_file" ]] && continue
  if [[ "$d_file" == "FATAL" ]]; then
    echo "check-obligation-claims: FATAL — $d_text" >&2
    exit 1
  fi
  echo "  ✗  $d_file:$d_line $d_text"
  echo "       \`.text\`'s size is one \`abbrev\` in $ROOT_PINS — cite the SYMBOL, not the value"
  findings=$((findings + 1))
done <<< "$d_out"

if [[ $findings -eq 0 ]]; then
  echo "check-obligation-claims: OK — no unconverted-claim contradicted by GuestImageEntries, no hand-written coverage figure, no prose contradicting textSizeBytes. (Counts: see check-embedded-counts.sh.)"
  exit 0
fi

echo
echo "check-obligation-claims: $findings finding(s)."
cat <<'EOF'

These rows are the dashboard other agents triage from, so a wrong one costs more
than it looks: #12129 exists because a stale "blocked on transcription" line made
the highest-leverage startable proof in the tree read as unstartable.

  class A — the symbol IS in the deployed image, so "unconverted" is false. Narrow
            the blocker to the DOMAIN that is genuinely missing — the way
            obligation 7/10 now says "for the GENERAL/HIT domain" — or drop it
            from `EvmAsm/Progress/Obligations.lean`; then refresh that row's
            `auditedAt` and re-run `scripts/drift-report.sh --write`.
  class C — delete the figure and point at docs/4ch8f-guest-image-coverage.md.
EOF

[[ $STRICT -eq 1 ]] && exit 1
exit 0
