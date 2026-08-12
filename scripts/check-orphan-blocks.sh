#!/usr/bin/env bash
# check-orphan-blocks.sh — CI entry for GH #12259.
#
# Flags basic blocks with no incoming branch/jump edge (excluding symbol
# entries) on the *linked* guest ELF. Catches the #12254 defect class
# (orphaned status-0 block after a dropped beqz). Does NOT catch misaimed
# mid-sequence targets (#12256); that half is explicitly out of scope.
#
# Belongs in the BUILD job (needs gen-out/regionmap/stateless_guest.elf), not
# source-checks: edges do not respect function boundaries, so Lean-string
# fragment analysis false-orphans shared fail epilogues.
#
# Always run --self-test first in CI: a gate that cannot demonstrate catching
# a planted orphan is itself unaudited (#12236 / #12195).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

mode="${1:-}"
case "$mode" in
  ""|--report|--update-snapshot|--count-only)
    ;;
  --self-test)
    exec python3 scripts/orphan_blocks.py --self-test
    ;;
  *)
    echo "usage: $0 [--self-test|--report|--update-snapshot|--count-only]" >&2
    exit 2
    ;;
esac

python3 scripts/orphan_blocks.py --self-test
exec python3 scripts/orphan_blocks.py ${mode:+"$mode"}
