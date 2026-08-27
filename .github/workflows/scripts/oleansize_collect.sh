#!/usr/bin/env bash
# oleansize_collect.sh — capture per-module compiled-artifact byte sizes for the
# EvmAsm tree and merge them into lakeprof.topn.json (report R-F2).
#
# WHY a size metric alongside lakeprof time: build TIME on a shared CI runner is
# noisy (R-F2 keeps it deliberately threshold-free). Compiled-artifact SIZE is
# DETERMINISTIC for a given commit, so a regression shows up as a monotone size
# jump even when the wall-clock is too noisy to read. Still trend-only, NEVER a
# gate, and NEVER a reason to bump maxHeartbeats (R-F2 / non-goals).
#
# ⚠️ THE MODULE SYSTEM SPLIT THIS METRIC IN TWO, AND THE ORIGINAL READING OF IT
# IS NOW WRONG. A migrated module emits THREE artifacts:
#
#   Foo.olean          the public INTERFACE — what every downstream module loads
#   Foo.olean.private  the proof terms — loaded by nobody downstream
#   Foo.olean.server   editor metadata
#
# This script used to collect `*.olean` and call it "the proof-SIZE half of the
# cost trend". Post-migration that is no longer what it measures: proofs moved
# into `.olean.private`, which `-name '*.olean'` does NOT match. Measured on the
# EVM tree, public is 130.3 MB against 842.9 MB private — so the old trend line
# silently became an INTERFACE-size trend for 1848 modules.
#
# Both numbers are worth having, and they answer different questions:
#
#   public  — the interface. Falls when a definition stops being `@[expose]`d.
#             This is the meter for the exposure-narrowing pass, because
#             `import-graph-metrics.py` cannot see that change at all (it reads
#             the import graph, which un-exposing does not touch).
#   private — the original proof-bloat signal. A ballooning proof (the n=4
#             division proofs are the prime suspects) lands here now.
#
# CAVEAT for whoever reads the trend: byte sizes also step-change on a
# `lean-toolchain` bump (new compiler / metadata layout) with ZERO proof change.
# Compare sizes WITHIN a toolchain era, not across one — a jump coinciding with
# a toolchain bump is not proof bloat.
#
# Inputs (env):
#   OLEANSIZE_TOP_N    — how many largest modules to keep (default 30)
#   TOPN_JSON          — lakeprof.topn.json to merge into (default ./lakeprof.topn.json)
#   LAKE_BUILD_LIB     — olean root. Current Lean lays oleans under
#                        .lake/build/lib/lean/EvmAsm (older layouts used
#                        .lake/build/lib/EvmAsm). Default tries the modern path
#                        and falls back to the legacy one.
#
# Pure bash + python3 (for the JSON merge). No network.
set -euo pipefail

TOP_N="${OLEANSIZE_TOP_N:-30}"
TOPN_JSON="${TOPN_JSON:-./lakeprof.topn.json}"
LIB="${LAKE_BUILD_LIB:-}"
if [[ -z "$LIB" ]]; then
  for cand in .lake/build/lib/lean/EvmAsm .lake/build/lib/EvmAsm; do
    [[ -d "$cand" ]] && { LIB="$cand"; break; }
  done
  LIB="${LIB:-.lake/build/lib/lean/EvmAsm}"
fi

if [[ ! -d "$LIB" ]]; then
  echo "oleansize_collect: $LIB not found (build incomplete?); skipping." >&2
  exit 0
fi

# `find -printf` is GNU-only. On BSD/macOS it prints nothing and, with the
# `2>/dev/null || true` below, the script would report "merged 0 sizes" and exit
# 0 — a SILENT SKIP, which is the failure mode this repo has been bitten by
# before (the byte-identity gates quietly did nothing on macOS). Detect the
# capability once and fall back to `stat`, so the metric is reproducible on a
# maintainer's laptop and not only on the CI runner.
sizes_of() {  # $1 = -name pattern; emits "<bytes>\t<path>"
  if find "$LIB" -maxdepth 0 -printf '' >/dev/null 2>&1; then
    find "$LIB" -name "$1" -printf '%s\t%p\n' 2>/dev/null
  else
    find "$LIB" -name "$1" -type f -exec stat -f '%z%t%N' {} + 2>/dev/null
  fi
}

# module path (EvmAsm.Foo.Bar) + byte size, largest first, top N.
tmp="$(mktemp)"
tmp_priv="$(mktemp)"
# `|| true`: head closes the pipe after N lines, which SIGPIPEs find/sort;
# under `set -o pipefail` that would otherwise abort the script.
sizes_of '*.olean' | sort -rn | head -n "$TOP_N" > "$tmp" || true
sizes_of '*.olean.private' | sort -rn | head -n "$TOP_N" > "$tmp_priv" || true

# Tree-wide totals. These, not the top-N, are the trend worth reading: the
# public total is the exposure meter and the private total is the proof-bloat
# meter. Emitted as one "<kind> <bytes> <count>" line per kind.
tmp_tot="$(mktemp)"
for kind in 'olean' 'olean.private' 'olean.server'; do
  sizes_of "*.${kind}" \
    | awk -v k="$kind" '{s+=$1; n++} END {printf "%s %d %d\n", k, s+0, n+0}' \
    >> "$tmp_tot"
done

export TMP_LIST="$tmp" TMP_PRIV="$tmp_priv" TMP_TOT="$tmp_tot" LIB_ROOT="$LIB" \
       TOPN_JSON_ABS="$(readlink -f "$TOPN_JSON" 2>/dev/null || echo "$TOPN_JSON")" TOP_N
python3 - <<'PY'
import json, os


def read(env_key, suffix):
    rows = []
    with open(os.environ[env_key], encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            size, path = line.split("\t", 1)
            # .lake/build/lib/[lean/]EvmAsm/Foo/Bar.olean -> EvmAsm.Foo.Bar
            rel = path.split("/lib/", 1)[-1]
            if rel.startswith("lean/"):      # strip the modern layout segment
                rel = rel[len("lean/"):]
            mod = rel[:-len(suffix)].replace("/", ".") if rel.endswith(suffix) else rel
            rows.append({"module": mod, "bytes": int(size)})
    return rows


rows = read("TMP_LIST", ".olean")
priv = read("TMP_PRIV", ".olean.private")

totals = {}
with open(os.environ["TMP_TOT"], encoding="utf-8") as f:
    for line in f:
        parts = line.split()
        if len(parts) == 3:
            kind, byts, cnt = parts
            key = {"olean": "public", "olean.private": "private",
                   "olean.server": "server"}[kind]
            totals[f"{key}_bytes"] = int(byts)
            totals[f"{key}_modules"] = int(cnt)

# The raw public total counts UNMIGRATED modules too, and those have no split at
# all — everything sits in `.olean`. Mixing them in makes the public share look
# far worse than it is and makes the trend unreadable while the migration is
# partial. So report the split-only figures beside the raw ones: `split_public`
# is the public half of modules that actually HAVE a private half, and it is the
# number the exposure pass moves.
split_pub = split_prv = split_n = 0
lib = os.environ.get("LIB_ROOT", "")
if lib:
    for dirpath, _dirnames, filenames in os.walk(lib):
        for fn in filenames:
            if not fn.endswith(".olean.private"):
                continue
            base = os.path.join(dirpath, fn[:-len(".private")])
            try:
                split_pub += os.path.getsize(base)
                split_prv += os.path.getsize(os.path.join(dirpath, fn))
                split_n += 1
            except OSError:
                pass
    totals["split_public_bytes"] = split_pub
    totals["split_private_bytes"] = split_prv
    totals["split_modules"] = split_n

p = os.environ["TOPN_JSON_ABS"]
data = {}
if os.path.exists(p):
    try:
        with open(p, encoding="utf-8") as f:
            data = json.load(f) or {}
    except Exception:
        data = {}
# `olean_sizes` keeps its existing meaning and shape so the append-only history
# on `benchmark-history` stays readable across the change.
data["olean_sizes"] = rows
data["olean_private_sizes"] = priv
data["olean_totals"] = totals
with open(p, "w", encoding="utf-8") as f:
    json.dump(data, f, sort_keys=True)

pub_b = totals.get("public_bytes", 0)
prv_b = totals.get("private_bytes", 0)
share = (100.0 * pub_b / (pub_b + prv_b)) if (pub_b + prv_b) else 0.0
print(f"oleansize_collect: merged {len(rows)} public + {len(priv)} private "
      f"sizes into {p}")
print(f"oleansize_collect: ALL     public {pub_b/1e6:.1f} MB over "
      f"{totals.get('public_modules', 0)} modules; "
      f"private {prv_b/1e6:.1f} MB over {totals.get('private_modules', 0)}; "
      f"public share {share:.1f}%")
sp, spr, sn = (totals.get("split_public_bytes", 0),
               totals.get("split_private_bytes", 0),
               totals.get("split_modules", 0))
if sn:
    sshare = 100.0 * sp / (sp + spr) if (sp + spr) else 0.0
    print(f"oleansize_collect: MIGRATED public {sp/1e6:.1f} MB over {sn} "
          f"modules; private {spr/1e6:.1f} MB; public share {sshare:.1f}%  "
          f"<-- the exposure meter")
if totals.get("public_modules", 0) == 0:
    raise SystemExit("oleansize_collect: found NO oleans — refusing to record "
                     "an empty measurement as if it were a real one")
PY
rm -f "$tmp" "$tmp_priv" "$tmp_tot"
