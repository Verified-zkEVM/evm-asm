#!/usr/bin/env bash
# codegen-zisk-selfdestruct-balance-transfer-check.sh -- verify the
# SELFDESTRUCT account-RLP balance transfer helper against Python vectors.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/mpt-set"
echo "==> generate vectors via the Python account-RLP reference"
uv run --directory execution-specs --quiet python3 "$REPO_ROOT/scripts/mpt_ref.py" "$VDIR"

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_selfdestruct_balance_transfer probe ELF"
lake exe codegen --program zisk_selfdestruct_balance_transfer --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_selfdestruct_balance_transfer"

fail=0
for name in sdbt_diff sdbt_same_keep sdbt_same_burn; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_selfdestruct_balance_transfer.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }

  status="$(od -An -tu8 -j 248 -N 8 "$out" | tr -d ' \n')"
  origin_len="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  beneficiary_len="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
  origin_actual="$(xxd -p -s 16 -l "$origin_len" "$out" | tr -d '\n')"
  beneficiary_actual="$(xxd -p -s 128 -l "$beneficiary_len" "$out" | tr -d '\n')"
  origin_expected="$(cat "$VDIR/$name.origin.expected")"
  beneficiary_expected="$(cat "$VDIR/$name.beneficiary.expected")"

  if [[ "$status" == "0" && "$origin_actual" == "$origin_expected" && \
        "$beneficiary_actual" == "$beneficiary_expected" ]]; then
    echo "  PASS   $name"
  else
    echo "  FAIL   $name status=$status"
    echo "    origin expected:      $origin_expected"
    echo "    origin actual:        $origin_actual"
    echo "    beneficiary expected: $beneficiary_expected"
    echo "    beneficiary actual:   $beneficiary_actual"
    fail=1
  fi
done

[[ "$fail" -eq 0 ]] && echo "==> PASS: SELFDESTRUCT balance transfer matches reference" \
  || { echo "==> FAIL"; exit 1; }
