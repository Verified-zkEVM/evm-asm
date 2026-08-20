#!/usr/bin/env bash
# Guest-image CodeReq coverage gate.
#
# 1. Self-test: the generator's planted-defect check must fail as designed, so a
#    detector that has silently stopped detecting is caught before the real run.
# 2. #11923/#12136/#12138 floor ratchet: covered bytes / converted entry count
#    must not drop below the recorded floors. Re-measure with
#    `python3 scripts/guest_image_coverage.py --write-floor` when landing a
#    legitimate decrease, and respect the documented slack windows
#    (COVERED_BYTES_FLOOR_SLACK / CONVERTED_COUNT_FLOOR_SLACK) — bumping the
#    floor to the live value zeroes the slack and serialises concurrent PRs.
#
# ⛔ The former `--check-doc` pass is gone: `docs/4ch8f-guest-image-coverage.md`
# is no longer tracked (see #12693). The doc is published nightly instead, so
# there is nothing in-tree to compare against. The FLOOR check is the part that
# carries the guarantee and it is retained deliberately — it is recorded AND
# gated, so it can fail when coverage regresses, which a regenerated report
# never can.
set -euo pipefail
exec python3 scripts/guest_image_coverage.py --check-floor
