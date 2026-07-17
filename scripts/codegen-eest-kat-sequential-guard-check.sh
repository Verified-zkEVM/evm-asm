#!/usr/bin/env bash
# codegen-eest-kat-sequential-guard-check.sh — the sequential-path 0-FA guard
# suite (bmvmx.5.5.15): runs every crafted adversarial KAT fixture family under
# fixtures/kat/ and requires ALL of them to match byte-exactly.
#
# Families (each ships a control the guest must ACCEPT and adversarial variants
# it must handle exactly per the reference):
#   fixtures/kat/eip8037-auth-retention/  — the bmvmx.5.5.11.1 exploit+control:
#     failed-7702 auth state-gas retention; exploit must be REJECTED.
#   fixtures/kat/prep-halt-auth/          — prep-halted (set_delegation OOG)
#     7702 tx: applied auth charge must be 0 via BAL rollback detection.
#   fixtures/kat/gas-gate-boundary/       — EIP-7778 sequential regular-gate
#     boundaries (accept at remaining, reject at remaining+1, failed-tx
#     full-burn accumulation) + calldata-floor clamp (floor, floor-1).
#   fixtures/kat/txcount-gate/            — the >16-tx inclusion-gate backstop
#     (bmvmx.5.5.15): eip8037_tx_gas_gate skips the sequential gate above 16
#     txs, so these 17-tx blocks (edge limit=remaining+1; limit>>used variant)
#     must still be REJECTED by the post-exec per-tx availability gate
#     (eip7778_remaining_block_gas_from_results). The txcount_gate2_control
#     accept case is intentionally NOT in this suite yet: it false-rejects
#     until the self-transfer over-charge FR (evm-asm-mkg26) is fixed; add it
#     as an accept-guard then.
#
# Every fixture's statelessOutputBytes is compared byte-exactly (verdict byte
# included), so the suite fails if any acceptance/rejection drifts.
#
# Regenerating fixtures: fill recipes live in the headers of the generator
# specs under scripts/kat/ (uv run fill ... --fork=Amsterdam in an
# execution-specs checkout at the pinned commit).
#
# Usage: scripts/codegen-eest-kat-sequential-guard-check.sh [extra harness args]
# Exit: 0 iff every case matches byte-exactly (--min-full enforced by the
# harness); 1 otherwise.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

EXPECTED_FULL=11  # 2 auth-retention + 2 prep-halt-auth + 5 gas-gate-boundary + 2 txcount-gate

EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat" \
EEST_RUN_DIR="${EEST_RUN_DIR:-gen-out/eest-run/kat-sequential-guard}" \
  scripts/codegen-eest-stateless-check.sh \
  --backend spike \
  --limit 64 \
  --jobs "${JOBS:-4}" \
  --no-verdict-debug \
  --min-full "$EXPECTED_FULL" \
  "$@"

echo "== OK: all $EXPECTED_FULL sequential-path guard cases byte-exact =="
