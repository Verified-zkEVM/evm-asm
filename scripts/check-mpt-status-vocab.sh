#!/usr/bin/env bash
# GH #12234: MPT status vocabulary pin vs committed snapshot.
#
# Authority is scripts/mpt-status-vocab-expected.txt — NEVER derived from the
# live Lean source alone. Missing / truncated / mismatched → non-zero.
# Empty vocabulary is always a fail.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EXPECTED="$ROOT/scripts/mpt-status-vocab-expected.txt"
VOCAB="$ROOT/EvmAsm/Codegen/Programs/MptStatusVocab.lean"

die() { echo "check-mpt-status-vocab: $*" >&2; exit 1; }

[[ -f "$EXPECTED" ]] || die "missing committed snapshot: $EXPECTED"
[[ -s "$EXPECTED" ]] || die "committed snapshot is empty: $EXPECTED"
[[ -f "$VOCAB" ]] || die "missing vocab module: $VOCAB"
[[ -s "$VOCAB" ]] || die "vocab module is empty/truncated: $VOCAB"

# Extract layer.code=name from Lean abbrevs (Walk/Account/Cahsr namespaces).
extract_lean() {
  python3 - <<'PY' "$VOCAB"
import re, sys
src = open(sys.argv[1], encoding="utf-8").read()
layers = {
    "Walk": "walk",
    "Account": "account",
    "Cahsr": "cahsr",
}
out = []
for ns, layer in layers.items():
    # namespace Walk ... end Walk
    m = re.search(rf"namespace {ns}\n(.*?)end {ns}", src, re.S)
    if not m:
        sys.stderr.write(f"missing namespace {ns}\n")
        sys.exit(2)
    body = m.group(1)
    for name, code in re.findall(
        r"abbrev (\w+) : Nat := (\d+)", body
    ):
        out.append(f"{layer}.{code}={name}")
# Remap guards as equations
# accountOfWalk Walk.unresolved == Account.unresolved → remap.walk.3=account.4
# We encode the three contracted remaps from the typed #guards:
guards = [
    ("remap.walk.3=account.4",
     r"#guard accountOfWalk Walk\.unresolved == Account\.unresolved"),
    ("remap.account.4=cahsr.6",
     r"#guard cahsrOfAccount Account\.unresolved == Cahsr\.unresolved"),
    ("remap.walk.3=cahsr.6",
     r"#guard cahsrOfWalk Walk\.unresolved == Cahsr\.unresolved"),
]
for line, pat in guards:
    if not re.search(pat, src):
        sys.stderr.write(f"missing #guard for {line}\n")
        sys.exit(2)
    out.append(line)
print("\n".join(out))
PY
}

TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT
extract_lean >"$TMP" || die "failed to extract vocabulary from $VOCAB"

# Never-empty rule on the extracted side too.
[[ -s "$TMP" ]] || die "extracted vocabulary is empty (vacuous success forbidden)"

# Normalize: keep only non-comment non-blank lines, sort for set compare.
norm() {
  grep -vE '^\s*(#|$)' "$1" | sort
}

EXP_N="$(mktemp)"; ACT_N="$(mktemp)"
trap 'rm -f "$TMP" "$EXP_N" "$ACT_N"' EXIT
norm "$EXPECTED" >"$EXP_N"
norm "$TMP" >"$ACT_N"

if ! diff -u "$EXP_N" "$ACT_N" >/dev/null; then
  echo "check-mpt-status-vocab: snapshot mismatch (expected vs MptStatusVocab.lean)" >&2
  diff -u "$EXP_N" "$ACT_N" >&2 || true
  die "update BOTH $EXPECTED and MptStatusVocab.lean in the same PR"
fi

# Single-doc-home: fail only on a FULL cahsr/walk table restatement (multiple
# distinctive lines), not a one-line sibling docstring that still says
# "see MptStatusVocab" or copies a single status gloss.
python3 - <<'PY' "$ROOT/EvmAsm/Codegen/Programs" || die "full status table restated outside MptStatusVocab.lean"
import pathlib, re, sys
root = pathlib.Path(sys.argv[1])
cahsr_marks = [
    re.compile(r"0 = found in both state-trie"),
    re.compile(r"2 = state-trie mpt parse error"),
    re.compile(r"5 = code_hash not found in witness\.codes"),
]
walk_marks = [
    re.compile(r"0 \(found\) / 1 \(not found\) / 2 \(parse error\)"),
]
bad = []
for path in sorted(root.rglob("*.lean")):
    if path.name == "MptStatusVocab.lean":
        continue
    text = path.read_text(encoding="utf-8")
    if sum(1 for p in cahsr_marks if p.search(text)) >= 2:
        bad.append(str(path))
    if any(p.search(text) for p in walk_marks):
        bad.append(str(path))
if bad:
    print("\n".join(dict.fromkeys(bad)))
    sys.exit(1)
PY

# walk→cahsr raw tag is forbidden unless allow-listed (none by default).
if rg -n 'STATUS_VOCAB: walk→cahsr' "$ROOT/EvmAsm/Codegen/Programs" \
    "$ROOT/scripts/asm-fixtures" 2>/dev/null; then
  die "STATUS_VOCAB: walk→cahsr is forbidden (must remap walk→account→cahsr)"
fi

echo "check-mpt-status-vocab: OK (snapshot matches MptStatusVocab.lean)"
