#!/usr/bin/env bash
# check-doc-links.sh — existence gate for direct docs/*.md references.
#
# Scope is intentionally narrow and explicit: scan EvmAsm/, docs/, and the
# repository-root Markdown files for literal targets of the form
# docs/something.md, then require each target file to exist.  Nested paths such
# as docs/agents/foo.md and Markdown section anchors such as docs/foo.md#intro
# are out of scope.  Existence is a cheap grep-level invariant; validating
# section anchors needs a Markdown-aware check with different semantics.
#
# The live main-branch control is the removed merge-queue design note.  Its
# references are repaired in the same change rather than silently allowlisted.
set -euo pipefail
cd "$(dirname "$0")/.."

REFERENCE_RE='docs/[A-Za-z0-9_.-]+\.md'

scan_sources() {
  local root="$1"
  shift
  local refs
  local ref
  local total=0
  local -a missing=()

  refs="$(rg -o --no-filename "$REFERENCE_RE" "$@" | sort -u || true)"
  while IFS= read -r ref; do
    [[ -n "$ref" ]] || continue
    total=$((total + 1))
    if [[ ! -f "$root/$ref" ]]; then
      missing+=("$ref")
    fi
  done <<<"$refs"

  if ((${#missing[@]} != 0)); then
    echo "check-doc-links: FAIL — $total direct docs/*.md targets, ${#missing[@]} missing"
    for ref in "${missing[@]}"; do
      echo "  missing: $ref"
      rg -n -F -- "$ref" "$@" | sed 's/^/    referenced at: /' || true
    done
    return 1
  fi

  echo "check-doc-links: PASS — $total direct docs/*.md targets exist"
}

self_test() {
  local tmp
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' RETURN
  mkdir -p "$tmp/docs"
  : >"$tmp/docs/present.md"
  printf '%s\n' 'See docs/present.md and docs/planted-missing.md.' >"$tmp/README.md"

  if scan_sources "$tmp" "$tmp/README.md" >/dev/null; then
    echo "check-doc-links: SELF-TEST FAIL — planted missing target was accepted" >&2
    return 1
  fi

  : >"$tmp/docs/planted-missing.md"
  scan_sources "$tmp" "$tmp/README.md"
  echo "check-doc-links: SELF-TEST PASS — planted missing target failed, restored target passed"
}

if [[ "${1:-}" == "--self-test" ]]; then
  self_test
  exit 0
fi

mapfile -t sources < <(
  {
    rg --files EvmAsm docs -g '*.lean' -g '*.md'
    rg --files -g '*.md' | awk -F/ 'NF == 1'
  } | sort -u
)

if ((${#sources[@]} == 0)); then
  echo "check-doc-links: FAIL — no source files found" >&2
  exit 1
fi

self_test
scan_sources . "${sources[@]}"
