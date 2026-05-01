#!/usr/bin/env bash
# Append a lakeprof top-N record to the benchmark-history orphan branch.
#
# Mirrors the existing "Persist record to benchmark-history branch" step
# in `.github/workflows/benchmark.yml`, but writes a record with
# `kind="lakeprof"` carrying ONLY {commit, ref, run_id, top_modules}.
#
# Inputs (env):
#   GITHUB_TOKEN      — write-capable token for the repo
#   GITHUB_REPOSITORY — owner/repo (set by Actions)
#   GITHUB_SHA        — commit benchmarked
#   GITHUB_REF        — branch / ref triggering the run
#   GITHUB_RUN_ID     — run ID
#   GITHUB_EVENT_NAME — event ('schedule' / 'workflow_dispatch')
#   LAKEPROF_TOPN_JSON — path to lakeprof.topn.json (default: ./lakeprof.topn.json)
#
# The record's `kind` field distinguishes lakeprof entries from the
# build (wall+RSS) records appended by the sibling `benchmark` job.
# Existing pre-#949-followup records have neither key; consumers default
# to `"build"` when absent (per docs/949-lakeprof-design.md §5).

set -euo pipefail

TOPN_JSON="${LAKEPROF_TOPN_JSON:-./lakeprof.topn.json}"

if [ ! -f "$TOPN_JSON" ]; then
  echo "lakeprof_append: $TOPN_JSON not found, skipping history append" >&2
  exit 0
fi

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

git -c protocol.version=2 clone --no-checkout --filter=blob:none \
  "https://x-access-token:${GITHUB_TOKEN}@github.com/${GITHUB_REPOSITORY}.git" \
  "$tmpdir/history"
cd "$tmpdir/history"
git config user.name  'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

if git ls-remote --exit-code --heads origin benchmark-history >/dev/null 2>&1; then
  git fetch --depth=1 origin benchmark-history
  git checkout benchmark-history
else
  # The wall/RSS job creates this branch on first run; in the rare case
  # the lakeprof job races ahead, initialize a minimal orphan with an
  # empty log so the append still works. The README describes wall/RSS
  # fields; we intentionally do NOT rewrite it here so a later run of
  # the wall/RSS job populates the canonical README content.
  git checkout --orphan benchmark-history
  git rm -rf --quiet . 2>/dev/null || true
  printf '# benchmark-history\n\nSee benchmark.yml for schema.\n' > README.md
  : > history.jsonl
fi

export TOPN_JSON_ABS="$(cd "$OLDPWD" && readlink -f "$TOPN_JSON")"
export TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
script="$tmpdir/append_record.py"
cat > "$script" <<'PY'
import json, os
with open(os.environ["TOPN_JSON_ABS"], "r", encoding="utf-8") as f:
    topn = json.load(f).get("top_modules") or []
rec = {
    "kind":         "lakeprof",
    "commit":       os.environ["GITHUB_SHA"],
    "ref":          os.environ["GITHUB_REF"],
    "timestamp":    os.environ["TIMESTAMP"],
    "trigger":      os.environ["GITHUB_EVENT_NAME"],
    "run_id":       os.environ["GITHUB_RUN_ID"],
    "top_modules":  topn,
}
with open("history.jsonl", "a", encoding="utf-8") as f:
    f.write(json.dumps(rec, sort_keys=True) + "\n")
PY
python3 "$script"

git add history.jsonl README.md
git commit -m "lakeprof: ${GITHUB_SHA::12} top=$(python3 -c 'import json,os; print(len(json.load(open(os.environ["TOPN_JSON_ABS"])).get("top_modules") or []))')" \
  --allow-empty

# Push with retries: the workflow's `concurrency.group` should serialize
# weekly runs, but a manual workflow_dispatch could still race against
# the cron run, or against the sibling benchmark job's own append.
for attempt in 1 2 3; do
  if git push origin benchmark-history; then
    echo "lakeprof history push: ok on attempt $attempt"
    exit 0
  fi
  echo "lakeprof history push: attempt $attempt failed, refetching + re-applying" >&2
  git fetch origin benchmark-history
  git reset --hard origin/benchmark-history
  python3 "$script"
  git add history.jsonl README.md
  git commit -m "lakeprof: ${GITHUB_SHA::12} top=$(python3 -c 'import json,os; print(len(json.load(open(os.environ["TOPN_JSON_ABS"])).get("top_modules") or []))')" \
    --allow-empty
  sleep 5
done

echo "lakeprof_append: push retries exhausted" >&2
exit 1
