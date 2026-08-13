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
#   C. A `.text` coverage percentage hand-written into PLAN.md. That number is
#      GENERATED into docs/4ch8f-guest-image-coverage.md by
#      scripts/guest_image_coverage.py and moves every time a `_prog` lands.
#      PLAN.md carried "~24.65%" when the generated value had reached 35.36% —
#      stale by more than ten points. A number that can be generated must not
#      be hand-maintained.
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
#   scripts/check-obligation-claims.sh --strict # exit 1 on any finding
#
set -uo pipefail
cd "$(dirname "$0")/.."

STRICT=0
[[ "${1:-}" == "--strict" ]] && STRICT=1

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

PROGRESS="PROGRESS.md"
OBLIGATIONS="EvmAsm/Progress/Obligations.lean"
PLAN="PLAN.md"
COVERAGE_DOC="docs/4ch8f-guest-image-coverage.md"
ENTRIES="EvmAsm/Codegen/Proofs/GuestImageEntries.lean"

findings=0

# ---------------------------------------------------------------------------
# Class A — an infra blocker naming a declaration that exists.
# ---------------------------------------------------------------------------
# Parsed from the RENDERED table in PROGRESS.md rather than the Lean source, for
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
    r'UNCONVERTED|unconverted|untranscribed|NOT[ _]CONVERTED'
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
# The absence claim is about the DISPATCHER (`dispatchLoop_prog` genuinely does
# not exist); the two converted symbols in the NEXT sentence carry entirely
# different claims ("no machine post yet", "compose still open"), both true.
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
  echo "check-obligation-claims: $PROGRESS or $ENTRIES missing — class A skipped." >&2
fi

# ---------------------------------------------------------------------------
# Class B — NOT implemented here: `scripts/check-embedded-counts.sh` already
# covers it, with the identical pattern `[0-9]+ (rows|proven|conditional|partly)`
# over the same file, and is itself attributed to #12129. Duplicating it would
# just mean two gates to keep in sync. Run both; this one deliberately has no
# class-B branch.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Class C — a hand-written coverage percentage in PLAN.md.
# ---------------------------------------------------------------------------
if [[ -f "$PLAN" ]]; then
  # A line is a finding when it carries a decimal percentage AND talks about
  # coverage AND mentions `.text` — all three, so PLAN.md's other percentages
  # (benchmark deltas, proof-tier shares) are left alone.
  #
  # ⚠️ Do NOT try to match the phrase "`.text` coverage" as contiguous text. The
  # two real instances are "~24.65% `.text` coverage" and "23.76% of `.text`" —
  # different word order, with markdown backticks in the middle. An earlier
  # version of this check anchored on `\.text coverage` and silently matched
  # NEITHER; a negative-control run (reintroduce the stale figure, confirm the
  # gate fires) is what caught that, and is also what turned up the second
  # instance, which #12129 never mentioned. Keep the three conditions
  # independent.
  while IFS= read -r hit; do
    [[ -z "$hit" ]] && continue
    echo "  ✗  $PLAN hand-writes a .text coverage percentage: $hit"
    echo "       that number is generated into $COVERAGE_DOC by scripts/guest_image_coverage.py"
    findings=$((findings + 1))
  done < <(grep -nE '[0-9]+\.[0-9]+%' "$PLAN" 2>/dev/null \
             | grep -i 'coverage' | grep -F '.text')
fi

if [[ $findings -eq 0 ]]; then
  echo "check-obligation-claims: OK — no unconverted-claim contradicted by GuestImageEntries, no hand-written coverage figure. (Counts: see check-embedded-counts.sh.)"
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
            `auditedAt` and re-run `scripts/progress-report.sh --write`.
  class C — delete the figure and point at docs/4ch8f-guest-image-coverage.md.
EOF

[[ $STRICT -eq 1 ]] && exit 1
exit 0
