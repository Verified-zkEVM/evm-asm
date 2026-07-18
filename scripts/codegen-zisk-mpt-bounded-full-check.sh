#!/usr/bin/env bash
# Run every bounded-MPT KAT against one force-relinked codegen executable.
set -euo pipefail
cd "$(dirname "$0")/.."

bash scripts/codegen-force-relink.sh
export CODEGEN_RELINKED_SESSION=1

count=0
for check in scripts/codegen-zisk-mpt-bounded-*-check.sh; do
  [[ "$check" == "scripts/codegen-zisk-mpt-bounded-full-check.sh" ]] && continue
  bash "$check"
  count=$((count + 1))
done
echo "PASS: $count bounded-MPT KATs share one clean codegen relink"
