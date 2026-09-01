#!/usr/bin/env bash
# Append records to an append-only orphan history branch.
#
# This is the shared clone/initialize/append/retry mechanism used by history
# producers.  Callers own record construction; this helper owns the durable
# branch update so each history cannot grow a subtly different push path.
#
# Required arguments:
#   --branch NAME          orphan branch to update
#   --history-file PATH    file in that branch receiving JSONL records
#   --record-file PATH     local file whose non-empty lines are appended
#   --message MESSAGE      commit message
#
# Optional:
#   --readme-file PATH     README used when the orphan branch is initialized
#   --origin URL           repository URL (defaults to GITHUB_TOKEN/repository)
#   --retries N            push attempts (default: 3)
#
# The helper clones a fresh temporary worktree for every push attempt.  A
# rejected push therefore replays the same records on top of the newest remote
# branch without reset/rebase, and a retry can never duplicate records from a
# failed attempt.

set -euo pipefail

BRANCH=""
HISTORY_FILE=""
RECORD_FILE=""
README_FILE=""
COMMIT_MESSAGE=""
ORIGIN_URL="${HISTORY_ORIGIN_URL:-}"
RETRIES="${HISTORY_PUSH_RETRIES:-3}"

usage() {
  cat <<'USAGE'
Usage: orphan-history-append.sh --branch NAME --history-file PATH \
  --record-file PATH --message MESSAGE [--readme-file PATH] [--origin URL]
USAGE
}

require_arg() {
  local opt="$1"
  if [[ $# -lt 2 || -z "${2:-}" ]]; then
    echo "$opt requires an argument" >&2
    usage >&2
    exit 2
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --branch) require_arg "$1" "${2:-}"; BRANCH="$2"; shift 2 ;;
    --history-file) require_arg "$1" "${2:-}"; HISTORY_FILE="$2"; shift 2 ;;
    --record-file) require_arg "$1" "${2:-}"; RECORD_FILE="$2"; shift 2 ;;
    --readme-file) require_arg "$1" "${2:-}"; README_FILE="$2"; shift 2 ;;
    --message) require_arg "$1" "${2:-}"; COMMIT_MESSAGE="$2"; shift 2 ;;
    --origin) require_arg "$1" "${2:-}"; ORIGIN_URL="$2"; shift 2 ;;
    --retries) require_arg "$1" "${2:-}"; RETRIES="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

[[ -n "$BRANCH" && -n "$HISTORY_FILE" && -n "$RECORD_FILE" && -n "$COMMIT_MESSAGE" ]] || {
  echo "branch, history-file, record-file and message are required" >&2
  usage >&2
  exit 2
}
[[ "$BRANCH" != */* && "$BRANCH" != .* ]] || {
  echo "branch must be a simple branch name: $BRANCH" >&2
  exit 2
}
[[ "$HISTORY_FILE" != /* && "$HISTORY_FILE" != *..* ]] || {
  echo "history-file must be a relative path without '..': $HISTORY_FILE" >&2
  exit 2
}
[[ -r "$RECORD_FILE" ]] || { echo "record file is not readable: $RECORD_FILE" >&2; exit 2; }
[[ -z "$README_FILE" || -r "$README_FILE" ]] || {
  echo "README file is not readable: $README_FILE" >&2
  exit 2
}
[[ "$RETRIES" =~ ^[1-9][0-9]*$ ]] || { echo "retries must be positive: $RETRIES" >&2; exit 2; }

if [[ -z "$ORIGIN_URL" ]]; then
  : "${GITHUB_TOKEN:?GITHUB_TOKEN is required unless --origin is supplied}"
  : "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required unless --origin is supplied}"
  ORIGIN_URL="https://x-access-token:${GITHUB_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"
fi

record_count="$(awk 'NF { n++ } END { print n + 0 }' "$RECORD_FILE")"
[[ "$record_count" -gt 0 ]] || { echo "record file has no non-empty lines: $RECORD_FILE" >&2; exit 2; }

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

initialize_or_checkout() {
  local work="$1"
  git -c protocol.version=2 clone --no-checkout --filter=blob:none \
    "$ORIGIN_URL" "$work" >/dev/null
  cd "$work"
  git config user.name 'github-actions[bot]'
  git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
  if git ls-remote --exit-code --heads origin "$BRANCH" >/dev/null 2>&1; then
    git fetch --depth=1 origin "$BRANCH" >/dev/null
    git checkout -B "$BRANCH" FETCH_HEAD >/dev/null
    if [[ ! -f README.md ]]; then
      if [[ -n "$README_FILE" ]]; then
        cp "$README_FILE" README.md
      else
        printf '# %s\n\nAppend-only history written by the repository workflow.\n' "$BRANCH" > README.md
      fi
    fi
  else
    git checkout --orphan "$BRANCH" >/dev/null
    git rm -rf --quiet . 2>/dev/null || true
    if [[ -n "$README_FILE" ]]; then
      cp "$README_FILE" README.md
    else
      printf '# %s\n\nAppend-only history written by the repository workflow.\n' "$BRANCH" > README.md
    fi
    mkdir -p "$(dirname "$HISTORY_FILE")"
    : > "$HISTORY_FILE"
  fi
}

for attempt in $(seq 1 "$RETRIES"); do
  work="$tmpdir/attempt-$attempt"
  initialize_or_checkout "$work"
  mkdir -p "$(dirname "$HISTORY_FILE")"
  if [[ -s "$HISTORY_FILE" ]] && [[ "$(tail -c 1 "$HISTORY_FILE")" != $'\n' ]]; then
    printf '\n' >> "$HISTORY_FILE"
  fi
  cat "$RECORD_FILE" >> "$HISTORY_FILE"
  git add "$HISTORY_FILE" README.md
  git commit -m "$COMMIT_MESSAGE" --allow-empty >/dev/null
  if git push origin "$BRANCH" >/dev/null; then
    echo "orphan-history-append: pushed $record_count record(s) to $BRANCH (attempt $attempt)"
    exit 0
  fi
  echo "orphan-history-append: push attempt $attempt failed; retrying from remote head" >&2
  cd "$tmpdir"
  sleep 5
done

echo "orphan-history-append: push retries exhausted for $BRANCH" >&2
exit 1
