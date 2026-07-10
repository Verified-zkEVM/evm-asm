#!/usr/bin/env bash
set -euo pipefail

# Linked guest PCs in SAsm proofs must follow regenerated GuestAddrs symbols.
# 0x80000000 is the intentional relocation-invariance sentinel, not a linked PC.
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

hits="$({ grep -nEi "0x800[0-9a-f]{5}" EvmAsm/Codegen/Programs/*SAsm*.lean || true; } |
  awk '
    /0x80000000/ { next }
    /#guard[[:space:]]+GuestAddrs\.[A-Za-z0-9_]+[[:space:]]*=[[:space:]]*0x800[0-9A-Fa-f]{5}/ { next }
    { print }
  ')"

if [[ -n "$hits" ]]; then
  cat >&2 <<'EOF'
check-no-hardcoded-guest-pc.sh failed: linked guest PC literals must use
GuestAddrs.* symbolically. Keep only one literal anchor per routine:
  #guard GuestAddrs.<routine> = 0x...
EOF
  printf '%s\n' "$hits" >&2
  exit 1
fi

echo "check-no-hardcoded-guest-pc.sh: no hardcoded linked guest PCs."
