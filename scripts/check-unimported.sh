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
# module"). Tracked in issues #1209 / #1440.
#
# Usage:
#   scripts/check-unimported.sh           # exit 1 on any orphan
#   scripts/check-unimported.sh --report  # always exit 0; print full list
#
# History: an allow-list at scripts/unimported-allow.txt used to
# grandfather pre-existing orphans. It was drained to zero and removed
# in #1440; the script now enforces strict reachability with no
# escape hatch. If you genuinely need to land a temporary orphan, wire
# it into the nearest umbrella behind a `section`/no-op stub or revert
# this script — do NOT silently re-introduce an allow-list.
#
# POSIX/bash, no external deps beyond find/awk/sort.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# Library roots to start reachability from. A second `lean_lib` (e.g. splitting
# the CLI/test surface off the default target) adds its root module here; the
# zero-orphan property is then enforced over the UNION of the roots, with no
# allowlist. Keep in sync with `lakefile.toml`'s `[[lean_lib]]` roots.
ROOT_MODS=("EvmAsm")
LIB_DIR="EvmAsm"

mode="enforce"
if [[ ${1:-} == "--report" ]]; then
  mode="report"
fi

cd "$ROOT"

# Collect all module names from .lean files under EvmAsm/, plus the root.
mapfile -t all_modules < <(
  {
    printf '%s\n' "${ROOT_MODS[@]}"
    find "$LIB_DIR" -name '*.lean' -type f \
      | sed -e 's|\.lean$||' -e 's|/|.|g'
  } | LC_ALL=C sort -u
)

declare -A is_root
for r in "${ROOT_MODS[@]}"; do is_root["$r"]=1; done

# Map module -> file path. A root module lives at `<Root>.lean` beside the lib
# directory; every other module mirrors its dotted name.
mod_to_file() {
  local m="$1"
  if [[ -n "${is_root[$m]:-}" ]]; then echo "$m.lean"; return; fi
  echo "${m//./\/}.lean"
}

# Import edges for the whole tree in ONE call to the shared parser
# (scripts/lib/lean_imports.py). Previously this shelled out to awk once per
# file per BFS hop, which cost 54 s in CI; it is now well under a second.
#
# The shared parser is why this gate no longer mis-reads the module system: the
# old regex was anchored `^import <name>$`, so `public import`, `meta import`,
# `import all`, and a trailing `-- shake: keep` comment were all invisible and
# their edges silently vanished from the BFS — reporting perfectly-wired modules
# as orphans.
declare -A edges_of
while IFS=$'\t' read -r file _lineno _pub _meta _all target _raw; do
  [[ -z "${file:-}" ]] && continue
  m="${file%.lean}"; m="${m//\//.}"
  edges_of["$m"]+="$target"$'\n'
done < <(
  { printf '%s\n' "${ROOT_MODS[@]/%/.lean}"; find "$LIB_DIR" -name '*.lean' -type f; } \
    | xargs python3 "$(dirname "$0")/lib/lean_imports.py" --edges
)

direct_imports() {  # $1 = module name
  printf '%s' "${edges_of[$1]:-}"
}

# BFS from $ROOT_MOD using only edges into modules that exist on disk.
declare -A exists
for m in "${all_modules[@]}"; do
  exists["$m"]=1
done

declare -A visited
queue=("${ROOT_MODS[@]}")
while ((${#queue[@]})); do
  cur="${queue[0]}"
  queue=("${queue[@]:1}")
  if [[ -n "${visited[$cur]:-}" ]]; then
    continue
  fi
  visited["$cur"]=1
  while IFS= read -r dep; do
    [[ -z "$dep" ]] && continue
    if [[ -n "${exists[$dep]:-}" && -z "${visited[$dep]:-}" ]]; then
      queue+=("$dep")
    fi
  done < <(direct_imports "$cur")
done

# Compute orphans = all_modules \ visited (excluding root).
orphans=()
for m in "${all_modules[@]}"; do
  [[ -n "${is_root[$m]:-}" ]] && continue
  if [[ -z "${visited[$m]:-}" ]]; then
    orphans+=("$m")
  fi
done

if [[ "$mode" == "report" ]]; then
  printf 'Total .lean modules: %d\n' "${#all_modules[@]}"
  printf 'Reachable from %s: %d\n' "${ROOT_MODS[*]}" "${#visited[@]}"
  printf 'Orphans: %d\n' "${#orphans[@]}"
  if ((${#orphans[@]})); then
    printf '\nOrphan modules:\n'
    printf '  %s\n' "${orphans[@]}"
  fi
  exit 0
fi

if ((${#orphans[@]})); then
  cat >&2 <<EOF

==================================================================
Unimported-file check failed: ${#orphans[@]} orphan(s).

The following .lean file(s) exist under $LIB_DIR/ but are NOT
transitively imported from ${ROOT_MODS[*]}:

EOF
  printf '  %s\n' "${orphans[@]}" >&2
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

The historical allow-list (scripts/unimported-allow.txt) was
removed in #1440; do not re-introduce it without reviewer sign-off.

Tracked: issues #1209, #1440.
==================================================================
EOF
  exit 1
fi

printf 'unimported-file check: %d modules, %d reachable, 0 orphans.\n' \
  "${#all_modules[@]}" "${#visited[@]}"
