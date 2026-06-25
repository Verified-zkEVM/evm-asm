#!/usr/bin/env bash
# parity-check.sh [N] [SEED]
# Sample N blocks from the full manifest, run each on BOTH ziskemu and spike_run,
# and diff the 256-byte outputs. Byte-parity is the correctness gate for the
# SPIKE backend. Also prints per-backend wall time. Blocks that hit an
# unimplemented accelerator CSR (precompiles) are reported separately (expected
# to diverge until those CSRs land).
set -uo pipefail
cd "$(dirname "$0")/../.."   # worktree root
N="${1:-8}"; SEED="${2:-1}"
ELF="${GUEST_ELF:-$PWD/gen-out/stateless_guest_clzfix.elf}"
MAN="${MANIFEST:-$PWD/gen-out/loop/full/manifest.tsv}"
ZISKEMU="${ZISKEMU:-$HOME/.zisk/bin/ziskemu}"
SPIKE_RUN="$PWD/scripts/spike/spike_run"
STEPS="${EEST_STEPS:-5000000000}"
OUT="$PWD/gen-out/spike-parity"; mkdir -p "$OUT"
[[ -x "$SPIKE_RUN" ]] || { echo "build spike_run first (scripts/spike/build.sh)" >&2; exit 1; }

mapfile -t rows < <(python3 -c "
import random,sys
rows=[l.rstrip('\n').split('\t') for l in open('$MAN') if l.strip()]
rows=[r for r in rows if len(r)>=3 and len(r[2])==210]
random.Random($SEED).shuffle(rows)
for r in rows[:$N]: print(r[0]+'\t'+r[1])
")
match=0; differ=0; precompile=0
for line in "${rows[@]}"; do
  label="${line%%$'\t'*}"; inp="${line#*$'\t'}"
  [[ -f "$inp" ]] || inp="$(dirname "$MAN")/$inp"
  z0=$(date +%s.%N); "$ZISKEMU" -e "$ELF" -i "$inp" -o "$OUT/z.out" -n "$STEPS" >/dev/null 2>&1; z1=$(date +%s.%N)
  s0=$(date +%s.%N); "$SPIKE_RUN" "$ELF" "$inp" "$OUT/s.out" >"$OUT/slog" 2>&1; s1=$(date +%s.%N)
  zt=$(echo "$z1 - $z0"|bc); st=$(echo "$s1 - $s0"|bc)
  unimpl=$(grep -c UNIMPLEMENTED "$OUT/slog" 2>/dev/null||echo 0)
  if cmp -s "$OUT/z.out" "$OUT/s.out"; then
    printf 'MATCH    zisk=%.1fs spike=%.1fs (%.0fx)  %s\n' "$zt" "$st" "$(echo "$zt/$st"|bc)" "${label:0:55}"; match=$((match+1))
  elif [[ "$unimpl" -gt 0 ]]; then
    printf 'PRECOMP  (hit unimpl CSR; expected) %s\n' "${label:0:50}"; precompile=$((precompile+1))
  else
    printf 'DIFFER   %s\n' "${label:0:60}"; differ=$((differ+1))
    cmp -l "$OUT/z.out" "$OUT/s.out" 2>/dev/null|head -2
  fi
done
echo "==== parity: match=$match differ=$differ precompile=$precompile / $N ===="
[[ "$differ" -eq 0 ]]
