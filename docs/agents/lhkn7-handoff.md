# lhkn7 lane handoff

Current shipped slice #10520 routes MTx direct precompiles through the shared scalar kernel. It is fault removal, not FR clearance: exact-parent A/B attributed `22670` and `22671` FAULT-to-OK; post-rebase shipping sweep measured FA=0, FR=68, FAULT=0.

## Remaining slices

These are maintainer-order work; do not start them overnight. Each is a count==1-to-MTx superset slice requiring a full sweep and review.

- Core legacy: bv_fail 41, then 47.
- Type-4: bv_fail 40.
- Blob/receipt: bv_fail 53, 37, and 44.

Selector retirement requires every count==1 surface implemented by MTx, a valid forced count==1 diagnostic with no forced OK-to-FR transitions, and a final ordinary full-corpus measurement. No partial forced result authorizes selector retirement.

## Evidence and process

Keep forced attribution artifacts separate from current-main shipping artifacts; regenerate after a source/head change. The two-run template is: exact-parent full A/B with immutable recorded ELFs and denominator-checked transitions; rebase and four-step regen plus a third convergent relink; then a second full measurement of the immutable shipping ELF. State attribution and shipping measurements separately.

Record SHA/provenance before sweeps; use detached launches with named logs/PIDs; immutable-copy artifacts outside the repo and chmod 444; never rename or rebuild a read artifact; never substitute a different harness when blocked; record discarded runs as unknown.

Negative space: #10520 did not implement the withdrawn cold precharge, did not clear shipped FRs, and its forced-only clearance is not a shipping claim. Intrinsic recipient-charge duplication remains follow-up #10545.

## Origin of the procedure

The two-run procedure was derived from a failure: an early version staged 3000 gas into the dispatcher's execution-budget cell rather than an intrinsic accumulator. It flipped 2572 fixtures and required five refuted hypotheses before a hand-run and cell-by-cell parent control isolated the wrong destination. Treat provenance, isolation builds, and shipping-artifact measurement as requirements, not presentation polish.
