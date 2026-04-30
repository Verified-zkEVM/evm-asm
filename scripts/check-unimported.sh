#!/usr/bin/env bash
#
# check-unimported.sh — fail when a committed .lean file under EvmAsm/ is
# not transitively imported from the umbrella module EvmAsm.lean.
#
# Why this matters: lake will happily compile every reachable .lean file
# in the library directory, so an orphan file *appears* to build fine.
# But downstream consumers cannot `import` declarations that aren't
# wired into the module graph from the root, so these files quietly rot
# (see AGENTS.md §"New `.lean` files must be imported by the umbrella
# module"). Tracked in issue #1209.
#
# Usage:
#   scripts/check-unimported.sh           # exit 1 on any new orphan
#   scripts/check-unimported.sh --report  # always exit 0; print full list
#
# A grandfathered allow-list lives at scripts/unimported-allow.txt —
# one fully-qualified module name per line, '#' comments allowed.
# Trim that file as orphans are absorbed or deleted.
#
# POSIX/bash, no external deps beyond find/awk/sort/comm.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ROOT_MOD="EvmAsm"
LIB_DIR="EvmAsm"
ROOT_FILE="EvmAsm.lean"
ALLOW_FILE="$ROOT/scripts/unimported-allow.txt"

mode="enforce"
if [[ ${1:-} == "--report" ]]; then
  mode="report"
fi

cd "$ROOT"

# Collect all module names from .lean files under EvmAsm/, plus the root.
mapfile -t all_modules < <(
  {
    echo "$ROOT_MOD"
    find "$LIB_DIR" -name '*.lean' -type f \
      | sed -e 's|\.lean$||' -e 's|/|.|g'
  } | LC_ALL=C sort -u
)

# Map module -> file path.
mod_to_file() {
  local m="$1"
  if [[ "$m" == "$ROOT_MOD" ]]; then
    echo "$ROOT_FILE"
  else
    echo "${m//./\/}.lean"
  fi
}

# Extract direct EvmAsm.* imports from a file.
direct_imports() {
  local f="$1"
  awk '
    /^[[:space:]]*import[[:space:]]+EvmAsm(\.[A-Za-z0-9_]+)*[[:space:]]*$/ {
      sub(/^[[:space:]]*import[[:space:]]+/, "")
      sub(/[[:space:]]+$/, "")
      print
    }
  ' "$f"
}

# BFS from $ROOT_MOD using only edges into modules that exist on disk.
declare -A exists
for m in "${all_modules[@]}"; do
  exists["$m"]=1
done

declare -A visited
queue=("$ROOT_MOD")
while ((${#queue[@]})); do
  cur="${queue[0]}"
  queue=("${queue[@]:1}")
  if [[ -n "${visited[$cur]:-}" ]]; then
    continue
  fi
  visited["$cur"]=1
  f="$(mod_to_file "$cur")"
  if [[ ! -f "$f" ]]; then
    continue
  fi
  while IFS= read -r dep; do
    [[ -z "$dep" ]] && continue
    if [[ -n "${exists[$dep]:-}" && -z "${visited[$dep]:-}" ]]; then
      queue+=("$dep")
    fi
  done < <(direct_imports "$f")
done

# Compute unreached = all_modules \ visited (excluding root).
unreached=()
for m in "${all_modules[@]}"; do
  [[ "$m" == "$ROOT_MOD" ]] && continue
  if [[ -z "${visited[$m]:-}" ]]; then
    unreached+=("$m")
  fi
done

# Load allow-list.
declare -A allowed
if [[ -f "$ALLOW_FILE" ]]; then
  while IFS= read -r line; do
    line="${line%%#*}"
    line="${line//[[:space:]]/}"
    [[ -z "$line" ]] && continue
    allowed["$line"]=1
  done < "$ALLOW_FILE"
fi

# Partition unreached into known (allowed) and new (not allowed).
new_orphans=()
known_orphans=()
for m in "${unreached[@]}"; do
  if [[ -n "${allowed[$m]:-}" ]]; then
    known_orphans+=("$m")
  else
    new_orphans+=("$m")
  fi
done

# Detect stale allow-list entries (allowed but no longer orphaned, or file gone).
stale_allow=()
for m in "${!allowed[@]}"; do
  if [[ -z "${exists[$m]:-}" ]]; then
    stale_allow+=("$m  (file no longer exists)")
  elif [[ -n "${visited[$m]:-}" ]]; then
    stale_allow+=("$m  (now reachable)")
  fi
done

if [[ "$mode" == "report" ]]; then
  printf 'Total .lean modules: %d\n' "${#all_modules[@]}"
  printf 'Reachable from %s: %d\n' "$ROOT_MOD" "${#visited[@]}"
  printf 'Unreached: %d (%d allow-listed, %d new)\n' \
    "${#unreached[@]}" "${#known_orphans[@]}" "${#new_orphans[@]}"
  if ((${#new_orphans[@]})); then
    printf '\nNEW orphans (not in allow-list):\n'
    printf '  %s\n' "${new_orphans[@]}"
  fi
  if ((${#known_orphans[@]})); then
    printf '\nGrandfathered orphans:\n'
    printf '  %s\n' "${known_orphans[@]}"
  fi
  if ((${#stale_allow[@]})); then
    printf '\nStale allow-list entries:\n'
    printf '  %s\n' "${stale_allow[@]}"
  fi
  exit 0
fi

failed=0

if ((${#new_orphans[@]})); then
  cat >&2 <<EOF

==================================================================
Unimported-file check failed: ${#new_orphans[@]} new orphan(s).

The following .lean file(s) exist under $LIB_DIR/ but are NOT
transitively imported from $ROOT_FILE:

EOF
  printf '  %s\n' "${new_orphans[@]}" >&2
  cat >&2 <<EOF

Lake will still compile them because they live under the library
directory, but downstream files cannot \`import\` them and they
silently rot when the API around them changes.

To fix, do ONE of:

  1. Add an \`import <module>\` line to the appropriate umbrella
     (EvmAsm/Rv64.lean, EvmAsm/Evm64.lean, EvmAsm/EL.lean, or a
     deeper umbrella). See AGENTS.md §"New \`.lean\` files must be
     imported by the umbrella module" for placement rules.

  2. Delete the file if it is genuinely abandoned.

  3. (Last resort, with reviewer sign-off) add the module name to
     scripts/unimported-allow.txt with a \`#\` comment explaining
     why it cannot yet be wired up. Trim the entry as soon as the
     file is absorbed or removed.

Tracked: issue #1209.
==================================================================
EOF
  failed=1
fi

if ((${#stale_allow[@]})); then
  cat >&2 <<EOF

==================================================================
Stale allow-list entries in scripts/unimported-allow.txt:

EOF
  printf '  %s\n' "${stale_allow[@]}" >&2
  cat >&2 <<EOF

Please remove these lines — the listed modules are no longer
unimported orphans (either they were wired up, or the file was
deleted).
==================================================================
EOF
  failed=1
fi

if (( failed )); then
  exit 1
fi

printf 'unimported-file check: %d modules, %d reachable, %d grandfathered orphan(s).\n' \
  "${#all_modules[@]}" "${#visited[@]}" "${#known_orphans[@]}"
