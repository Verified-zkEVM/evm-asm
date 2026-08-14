#!/usr/bin/env bash
# check-rowed-liveness.sh — CI entry for GH #12381.
#
# Every distinct `routine "<sym>"` in EvmAsm/Progress/Routines.lean must be
# REACHED on the fresh link: a direct call/tail edge, a branch entry, an
# address materialization, or a dispatch-table word. Otherwise it needs an
# annotated exemption in scripts/rowed-liveness-allow.txt citing an issue.
#
# A row asserts that proven code is part of the guest's story. #11303's
# check-routine-liveness answers whether the symbol is PRESENT and accepts
# census presence as liveness by design; nothing answered whether it is CALLED.
# Three .proven rows turned out to sit on uncalled code (#12351); this gate's
# instrument found five more (#12386).
#
# Belongs in the BUILD job (needs gen-out/regionmap/stateless_guest.elf), like
# check-orphan-blocks.sh: reachability is a whole-image question and Lean-string
# fragment analysis cannot answer it.
#
# Always run --self-test first: a gate that cannot demonstrate catching a
# planted uncalled row is itself unaudited (#12236 / #12195). The self-test
# needs no ELF and no toolchain.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

mode="${1:-}"
case "$mode" in
  ""|--report)
    ;;
  --self-test)
    exec python3 scripts/rowed_liveness.py --self-test
    ;;
  *)
    echo "usage: $0 [--self-test|--report]" >&2
    exit 2
    ;;
esac

python3 scripts/rowed_liveness.py --self-test
exec python3 scripts/rowed_liveness.py ${mode:+"$mode"}
