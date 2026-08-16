#!/usr/bin/env bash
#
# check-transcription-queue.sh — CI entry point for the demand-first
# String→Program transcription queue (GH #12035).
#
# 1. Runs the generator's self-test: symbol-boundary matching, the
#    blockedBy-only obligation parse, the demand-over-cost weight ordering
#    (call-site popularity can never outrank one obligation row), the
#    `.replace` derivation shape, and the gated-tier row filter. A ranking
#    nobody has seen misfire is indistinguishable from one that cannot.
# 2. Asserts docs/4ch8f-transcription-queue.md matches what
#    `python3 scripts/transcription_queue.py --write-doc` emits from the live
#    obligations / residuals / registry / issue-snapshot inputs. Same shape as
#    check-guest-image-coverage.sh.
#
# The queue's inputs (Obligations.lean, Routines.lean, the issue snapshot) move
# more often than the layout inputs do, so expect this to ask for a
# regeneration more often than its guest-image sibling:
#
#     python3 scripts/transcription_queue.py --write-doc
#
# The one mode that touches the network, --refresh-issues, is NEVER run here:
# the doc renders from the committed scripts/proof-issues.json, so the same
# tree renders the same bytes with or without a GitHub token.
#
# Wired into scripts/check-build-parallel.sh codegen lane (GH #12496).
# Previously titled "CI entry point" but never invoked from build.yml /
# parallel — dormant-gate class, and on first measure was hiding real drift
# in docs/4ch8f-transcription-queue.md (unlike check-opcode-tables.sh, which
# was dormant but green). Regeneration:
#
#     python3 scripts/transcription_queue.py --write-doc

set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/transcription_queue.py --self-test
exec python3 scripts/transcription_queue.py --check-doc
