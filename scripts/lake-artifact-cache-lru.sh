#!/usr/bin/env bash
#
# lake-artifact-cache-lru.sh — size-capped LRU eviction for the Lake artifact
# cache (LAKE_ARTIFACT_CACHE=true).
#
# WHY THIS EXISTS
#   `lake cache` exposes only get/put/add/clean; `clean` wipes EVERYTHING,
#   which defeats the point of a shared cache. The artifact cache is
#   content-addressed, so it grows without bound: every distinct compiled
#   version of every file accumulates (branch switches, rebuilds after edits,
#   multiple checkouts on the same toolchain all deposit artifacts). This
#   script keeps the cache under a size cap by evicting the LEAST-RECENTLY-USED
#   artifacts (by atime), oldest first, down to a low-water target.
#
# WHY IT IS SAFE
#   The cache is a pure build accelerator. Deleting any artifact only causes
#   the next build that needs it to recompile it (a cache MISS, never
#   corruption). No proof, olean, or output is authoritative in the cache — the
#   authoritative copy is whatever a build produces.
#
# HARD-LINK AWARENESS (important)
#   Artifacts that a checkout has fetched are HARD-LINKED into that checkout's
#   .lake build tree, so the cache entry and the checkout entry share one inode.
#   Deleting the cache link of such a file reclaims ZERO disk (the inode
#   survives via the checkout link) AND would only force a needless recompile
#   later. Therefore this evictor considers ONLY cache-only artifacts
#   (st_nlink == 1) — i.e. old versions no longer referenced by any live
#   checkout. Those are exactly the entries whose deletion frees real disk, and
#   skipping nlink>1 entries means a running/active checkout is never disturbed.
#   (Per-checkout .lake dirs stay separate; this only touches the shared cache.)
#
# ATIME NOTE
#   The cache filesystem is typically mounted `relatime` (24h atime
#   granularity), which is sufficient for a daily/hourly size-cap LRU. If the
#   cache disk is ever mounted `noatime`, atime stops updating on read; switch
#   the sort key below from %A@ to %T@ (mtime) in that case.
#
# USAGE
#   lake-artifact-cache-lru.sh [--cache DIR] [--cap-gb N] [--target-gb N] [--dry-run]
#     --cache DIR     cache directory (default: $LAKE_CACHE_DIR, else the
#                     per-toolchain elan cache <toolchain>/lake/cache)
#     --cap-gb N      high-water: only evict when the cache exceeds this (default 120)
#     --target-gb N   low-water: evict down to about this (default 80)
#     --dry-run       print what would be removed; delete nothing
#
# Intended to run from cron. deps: bash, du, find, sort, awk, rm.
set -euo pipefail

DEFAULT_CACHE=/home/yoichi-bkp/.cache/lake-artifact-cache

default_cache() {
  if [ -n "${LAKE_CACHE_DIR:-}" ]; then printf '%s\n' "$LAKE_CACHE_DIR"; return; fi
  printf '%s\n' "$DEFAULT_CACHE"
}

CACHE="$(default_cache)"
CAP_GB=120
TARGET_GB=80
DRY=0
while [ $# -gt 0 ]; do
  case "$1" in
    --cache)     CACHE="$2"; shift 2;;
    --cap-gb)    CAP_GB="$2"; shift 2;;
    --target-gb) TARGET_GB="$2"; shift 2;;
    --dry-run)   DRY=1; shift;;
    -h|--help)   sed -n '2,40p' "$0"; exit 0;;
    *) echo "unknown arg: $1" >&2; exit 2;;
  esac
done

gib() { awk -v b="$1" 'BEGIN{printf "%.2f", b/1073741824}'; }

[ -d "$CACHE" ] || { echo "cache dir not present: $CACHE (nothing to do)"; exit 0; }

cap_bytes=$(( CAP_GB * 1073741824 ))
target_bytes=$(( TARGET_GB * 1073741824 ))

total=$(du -sb "$CACHE" 2>/dev/null | awk '{print $1}')
echo "cache=$CACHE size=$(gib "$total")G cap=${CAP_GB}G target=${TARGET_GB}G"
if [ "$total" -le "$cap_bytes" ]; then
  echo "under cap — no eviction needed."; exit 0
fi

need=$(( total - target_bytes ))
echo "over cap — reclaiming ~$(gib "$need")G of cache-only (nlink==1) artifacts, oldest atime first"

freed=0; removed=0; skipped_live=0
# Fields: atime | nlink | size | path  (oldest atime first).
while IFS='|' read -r atime nlink size path; do
  [ "$freed" -ge "$need" ] && break
  if [ "$nlink" -gt 1 ]; then skipped_live=$(( skipped_live + 1 )); continue; fi
  if [ "$DRY" = 1 ]; then
    echo "would rm ($(date -d "@${atime%.*}" '+%Y-%m-%d') $(gib "$size")G) $path"
  else
    rm -f -- "$path" || continue
  fi
  freed=$(( freed + size )); removed=$(( removed + 1 ))
done < <(find "$CACHE/artifacts" -type f -printf '%A@|%n|%s|%p\n' 2>/dev/null | sort -t'|' -n)

# Optional tidy: drop output-mapping JSONs not read in a week. A dangling
# mapping is harmless (it just resolves to a miss), so this is cosmetic.
if [ "$DRY" = 0 ]; then
  find "$CACHE/outputs" -type f -name '*.json' -atime +7 -delete 2>/dev/null || true
fi

new_total=$(du -sb "$CACHE" 2>/dev/null | awk '{print $1}')
echo "done — removed $removed artifact(s), reclaimed ~$(gib "$freed")G, skipped $skipped_live live (nlink>1); cache now $(gib "$new_total")G"
if [ "$freed" -lt "$need" ]; then
  echo "note: could not reach target using cache-only artifacts alone — remaining bulk is hard-linked into live checkouts (will become reclaimable once those rebuild/switch)."
fi
