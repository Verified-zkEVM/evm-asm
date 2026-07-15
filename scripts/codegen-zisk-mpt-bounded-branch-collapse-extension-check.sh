#!/usr/bin/env bash
# Deleting one branch child must merge its survivor extension's prefix.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"; [[ -n "$ZISKEMU" ]] || exit 1
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib,struct,sys
r=pathlib.Path(sys.argv[1])
old0=b'\xe2\xa0\x30'+b'\0'*31+b'\x80'
survivor_leaf=b'\xe3\xa0\x00'+b'\0'*31+b'\x80'  # 62 zero nibbles
old_ext=b'\xe2\x12\xa0'+keccak256(survivor_leaf)
def branch(xs):
 p=b''.join(b'\xa0'+x if x else b'\x80' for x in xs)+b'\x80';return b'\xf8'+bytes([len(p)])+p
old=branch([keccak256(old0),keccak256(old_ext)]+[None]*14)
expected=b'\xe4\x82\x00\x12\xa0'+keccak256(survivor_leaf)
nodes=[old,old0,old_ext,survivor_leaf];o=[];p=16
for n in nodes:o.append(p);p+=len(n)
sec=b''.join(struct.pack('<I',x) for x in o)+b''.join(nodes)
blob=struct.pack('<Q',len(sec))+keccak256(old)+b'\0'*64+struct.pack('<Q',0)+b'\0'*8+struct.pack('<Q',2)+sec
(r/'input').write_bytes(blob+b'\0'*(-len(blob)%8));(r/'expected').write_bytes(keccak256(expected))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 4000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib,struct,sys
r=pathlib.Path(sys.argv[1]);o=(r/'output').read_bytes();assert struct.unpack_from('<Q',o)[0]==0;assert o[8:40]==(r/'expected').read_bytes(),o[8:40].hex();print('PASS: bounded builder collapses a branch to its extension survivor')
PY
