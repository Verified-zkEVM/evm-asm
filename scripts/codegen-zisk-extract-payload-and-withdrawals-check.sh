#!/usr/bin/env bash
# codegen-zisk-extract-payload-and-withdrawals-check.sh -- verify
# extract_payload_and_withdrawals (bead evm-asm-fhsxz.2.4.2.3): locate the
# ExecutionPayload + withdrawals list within an SszStatelessInput.
#
# Python builds a synthetic StatelessInput (outer offset table -> NPR at [0];
# NPR -> ExecutionPayload at NPR+44; payload fixed region with the variable
# offsets set; N x 44-byte withdrawals between wd_off and bal_off). The probe
# navigates and outputs payload offset, withdrawals offset, count, and status;
# we diff all four.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/ssz-payload-wd"
mkdir -p "$VDIR"

echo "==> build synthetic SszStatelessInput cases + expected payload/withdrawals"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PY'
import sys, struct, os
VDIR = sys.argv[1]
u32 = lambda x: struct.pack("<I", x)

def write_case(name, n_withdrawals=3, *, wd_delta=0, bal_delta=0, status=0):
    withdrawals = b"".join(
        bytes([i + 1]) * 44 for i in range(n_withdrawals)
    )

    # ExecutionPayload: fixed region (540 B: variable offsets at
    # 436/504/508/528, u64s at 512/520/532) then variable data extra_data |
    # transactions | withdrawals | block_access_list.
    extra = b"xd"
    txs = b""
    bal = b"BAL"
    fixed = 540
    extra_off = fixed
    tx_off = extra_off + len(extra)
    wd_off = tx_off + len(txs)
    bal_off = wd_off + len(withdrawals)
    encoded_wd_off = wd_off + wd_delta
    encoded_bal_off = bal_off + bal_delta
    pf = bytearray(fixed)
    pf[436:440] = u32(extra_off)
    pf[504:508] = u32(tx_off)
    pf[508:512] = u32(encoded_wd_off)
    pf[528:532] = u32(encoded_bal_off)
    payload = bytes(pf) + extra + txs + withdrawals + bal

    # NewPayloadRequest: 44-byte fixed header
    # (offsets[0]=execution_payload=44), then the payload.
    npr = bytearray(44)
    npr[0:4] = u32(44)                  # execution_payload offset
    npr = bytes(npr) + payload

    # outer SszStatelessInput: offset table [npr, witness, chain_config,
    # public_keys] at +0/+4/+8/+12, then the sections.
    witness = b"WIT"
    cfg = b"CFG"
    pk = b"PK"
    o0 = 16
    o1 = o0 + len(npr)
    o2 = o1 + len(witness)
    o3 = o2 + len(cfg)
    outer = u32(o0) + u32(o1) + u32(o2) + u32(o3) + npr + witness + cfg + pk

    body = bytearray(outer)             # SSZ_BASE = input start (probe)
    while len(body) % 8:
        body.append(0)
    with open(os.path.join(VDIR, f"{name}.input"), "wb") as f:
        f.write(bytes(body))

    payload_off = o0 + 44               # outer NPR offset + NPR payload offset
    wd_off_abs = payload_off + encoded_wd_off
    if status == 0:
        expected = (payload_off, wd_off_abs, n_withdrawals, 0)
    else:
        expected = (0, 0, 0, status)
    with open(os.path.join(VDIR, f"{name}.expected"), "w") as f:
        f.write("%d %d %d %d\n" % expected)
    print(f"{name}: payload_off={payload_off} wd_off={wd_off_abs} count={n_withdrawals} status={status}")

write_case("valid")
write_case("bad-reversed", bal_delta=-200, status=1)
write_case("bad-remainder", bal_delta=1, status=1)
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_extract_payload_and_withdrawals probe ELF"
lake exe codegen --program zisk_extract_payload_and_withdrawals --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_extract_payload_and_withdrawals"

run_case() {
  local name="$1"
  local out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_extract_payload_and_withdrawals.elf" -i "$VDIR/$name.input" \
    -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR (ziskemu) $name"; exit 1; }
  local a_po a_wo a_ct a_st e_po e_wo e_ct e_st
  a_po="$(od -An -tu8 -j 0  -N 8 "$out" | tr -d ' \n')"
  a_wo="$(od -An -tu8 -j 8  -N 8 "$out" | tr -d ' \n')"
  a_ct="$(od -An -tu8 -j 16 -N 8 "$out" | tr -d ' \n')"
  a_st="$(od -An -tu8 -j 24 -N 8 "$out" | tr -d ' \n')"
  read e_po e_wo e_ct e_st < "$VDIR/$name.expected"
  if [[ "$a_po" == "$e_po" && "$a_wo" == "$e_wo" && "$a_ct" == "$e_ct" && "$a_st" == "$e_st" ]]; then
    echo "  PASS   $name payload_off=$a_po wd_off=$a_wo count=$a_ct status=$a_st"
  else
    echo "  FAIL   $name payload_off exp=$e_po act=$a_po ; wd_off exp=$e_wo act=$a_wo ; count exp=$e_ct act=$a_ct ; status exp=$e_st act=$a_st"
    echo "==> FAIL"; exit 1
  fi
}

run_case valid
run_case bad-reversed
run_case bad-remainder
echo "==> PASS: extract_payload_and_withdrawals matches reference"
