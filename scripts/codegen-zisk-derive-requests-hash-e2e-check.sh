#!/usr/bin/env bash
# codegen-zisk-derive-requests-hash-e2e-check.sh -- beads 8uld3.2.3 / 8uld3.4 integration.
#
# End-to-end: derive a withdrawal-request body from a synthetic WITHDRAWAL predeploy via the
# system-call harness, feed it (deposit/consolidation empty) through assemble_execution_requests
# -> execution_requests_hash -> requests_hash_verify, and assert the system-call-DERIVED body
# produces a deterministic requests_hash that verify ACCEPTS (match -> 0) and REJECTS when the
# expected (header) hash is corrupted (-> 1). This is the soundness shape block_verdict will use
# to stop trusting the SSZ-input execution_requests.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_derive_requests_hash_e2e ELF"
lake exe codegen --program zisk_derive_requests_hash_e2e --halt linux93 -o gen-out/zisk_drhe

python3 -c "import struct; open('gen-out/zisk_drhe.input','wb').write(struct.pack('<Q',0))"

"$ZISKEMU" -e gen-out/zisk_drhe.elf -i gen-out/zisk_drhe.input -o gen-out/zisk_drhe.output -n 4000000 \
  >gen-out/zisk_drhe.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_drhe.output', 'rb').read()
wbody_len     = struct.unpack('<Q', d[0:8])[0]
verify_zero   = struct.unpack('<Q', d[8:16])[0]
verify_match  = struct.unpack('<Q', d[16:24])[0]
verify_corrupt= struct.unpack('<Q', d[24:32])[0]
ok = (wbody_len == 76 and verify_zero == 1 and verify_match == 0 and verify_corrupt == 1)
print(f"  wbody_len={wbody_len} verify(zero)={verify_zero} verify(correct)={verify_match} verify(corrupt)={verify_corrupt}")
if not ok:
    print("  FAIL: derived withdrawal body did not yield a sound, verifiable requests_hash")
    print("  (expect wbody_len=76, verify(zero)=1, verify(correct)=0, verify(corrupt)=1)")
    raise SystemExit(1)
print("  PASS: system-call-derived withdrawal body -> requests_hash; verify accepts correct, rejects corrupted")
PY
