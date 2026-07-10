#!/usr/bin/env bash
#
# check-spec-refs.sh — machine-check the per-opcode execution-specs reference
# links (PROGRESS.md axis F row "Per-opcode reference-link audit", previously
# "manual; not yet machine-checked").
#
# What it checks (see scripts/check_spec_refs.py for the extraction rules):
#   * every `execution-specs/<path>.py` citation in EvmAsm/**/*.lean resolves
#     to a real file at the pinned submodule rev (BLOCKING);
#   * a `function `name`` anchor within two lines of the citation names a
#     `def`/`class` actually defined in the cited file (BLOCKING);
#   * `execution-specs/.../x.py` ellipsis citations are prose shorthand —
#     listed, never blocking (advisory);
#   * known-stale citations live in scripts/spec-refs-allow.txt (burndown,
#     axiom-allow.txt discipline: goal is an empty file).
#
# CALIBRATION — why blocking: a dead reference link is a real defect (the
# audit exists to catch spec drift), unlike naming nits; the allowlist keeps
# the gate green while known debt is burned down, and --self-test proves the
# checker flags planted violations (a gate that cannot demonstrate catching
# a violation is itself unaudited).
#
# Usage:
#   scripts/check-spec-refs.sh              # scan EvmAsm/ against the pin
#   scripts/check-spec-refs.sh --self-test  # planted-violation self-check
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check_spec_refs.py "$@"
