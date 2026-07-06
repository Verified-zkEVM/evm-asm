#!/usr/bin/env bash
# codegen-zisk-nonstorage-effect-aggregate-check.sh -- bead bmvmx.5.5.7.3.
# Known-answer check for nonstorage_effect_aggregate: the linear (radix-sort +
# run-compress) replacement for the O(N^2) per-account .Lbv_agg_loop. Three input
# records (A=0x11.., B=0x22.., A again) must aggregate to 2 distinct entries with
# first-seen pre + last-seen post:
#   A {pre_bal 10, post_bal 30, pre_nonce 1, post_nonce 3}
#   B {pre_bal 5,  post_bal 8,  post_nonce 1}
# sorted A<B.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
mkdir -p gen-out
echo "==> lake build codegen"; lake build codegen
echo "==> emit zisk_nonstorage_effect_aggregate ELF"
lake exe codegen --program zisk_nonstorage_effect_aggregate --halt linux93 -o gen-out/zisk_nonstorage_effect_aggregate
: > gen-out/zisk_nonstorage_effect_aggregate.input
"$ZISKEMU" -e gen-out/zisk_nonstorage_effect_aggregate.elf -i gen-out/zisk_nonstorage_effect_aggregate.input -o gen-out/zisk_nonstorage_effect_aggregate.output -n 100000000 >gen-out/zisk_nonstorage_effect_aggregate.emu.log 2>&1
python3 - <<\PY
import struct, sys
d = open("gen-out/zisk_nonstorage_effect_aggregate.output", "rb").read()
def u(o):
    return struct.unpack("<Q", d[o:o+8])[0] if o + 8 <= len(d) else None
ok = (
    u(0)  == 0    and  # status
    u(8)  == 2    and  # distinct count
    u(16) == 10   and  # A.pre_bal[31]   (first-seen)
    u(24) == 30   and  # A.post_bal[31]  (last-seen)
    u(32) == 1    and  # A.pre_nonce     (first-seen)
    u(40) == 3    and  # A.post_nonce    (last-seen)
    u(48) == 0x11 and  # A.addr[0]
    u(56) == 5    and  # B.pre_bal[31]
    u(64) == 8    and  # B.post_bal[31]
    u(72) == 1    and  # B.post_nonce
    u(80) == 0x22      # B.addr[0]
)
print(f"  status={u(0)} count={u(8)} A.pre={u(16)} A.post={u(24)} A.pn={u(32)} A.poN={u(40)} A.addr={hex(u(48) or 0)} B.pre={u(56)} B.post={u(64)} B.poN={u(72)} B.addr={hex(u(80) or 0)}")
sys.exit(0 if ok else 1)
PY
echo; echo "==> PASS: nonstorage_effect_aggregate dedups by address with first-pre / last-post"
