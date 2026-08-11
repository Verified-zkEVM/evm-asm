#!/usr/bin/env bash
#
# check-guest-image-coverage.sh — CI entry point.
#
# 1. Asserts that docs/4ch8f-guest-image-coverage.md matches what
#    `python3 scripts/guest_image_coverage.py --write-doc` would emit from the
#    live linker-facts / manifest / #guard-pin inputs. Fails the build on
#    drift. Same shape as scripts/check-drift.sh.
# 2. #11923 floor ratchet: covered bytes and converted-entry count must not
#    drop below EXPECTED_*_FLOOR in guest_image_coverage.py (absolute bytes,
#    not ratio — .text growth alone must not fail). Bump the floor only in
#    the same commit that lands a conversion.
#
# Why: the doc embeds generator numbers (§1 summary, §3 gap table). The tsv
# inputs were already drift-guarded, but the doc was not — so its figures
# went stale invisibly (documented 24.19% / 912 / 340 while live was
# 23.65% / 902 / 330). The doc is now fully generated from
# scripts/asm-fixtures/guest-image-coverage-template.md (prose + slots, no
# figures); this guard is the regenerate-and-compare half of that move.
# §2 (gap clusters) is editorial and deliberately NOT pinned — the doc says
# so at the head of that section.

set -euo pipefail
cd "$(dirname "$0")/.."
# --check-doc already enforces the floor after the doc compare; a second
# --check-floor pass makes the floor line visible even when the doc is clean.
python3 scripts/guest_image_coverage.py --check-doc
exec python3 scripts/guest_image_coverage.py --check-floor
