#!/usr/bin/env bash
# conformance/run.sh — live-chain conformance harness for evm-asm.
#
# Runs REAL Ethereum data through the actual verified evm-asm RISC-V guest on
# the Zisk emulator, and cross-checks the result against the live chain.
#
#   ./run.sh                 narrated demo (default), live RPC
#   ./run.sh --deep          + proof deep-dives (kernel theorem + cycle bound)
#   ./run.sh --no-net        offline: use vendored canned chain data
#   ./run.sh --report        opcode-coverage scorecard over a live block
#   ./run.sh --check-manifest verify capabilities.json matches PROGRESS.md
#   ./run.sh --auto          no interactive pauses; PACE=0 for instant output
#
# Env: RPC_URL=... GUEST_ELF=... ZISKEMU=... PACE=<sec> NO_COLOR=1
#
# See README.md for scope, what it does NOT claim yet, and the maturity roadmap.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$HERE/lib.sh"
# shellcheck source=candidates.env
source "$HERE/candidates.env"

MODE="demo"; export DEEP="${DEEP:-0}"; NO_NET=0; export AUTO="${AUTO:-0}"
for a in "$@"; do
  case "$a" in
    --demo)            MODE="demo" ;;
    --report)          MODE="report" ;;
    --check-manifest)  MODE="check-manifest" ;;
    --deep)            DEEP=1 ;;
    --no-net)          NO_NET=1 ;;
    --auto)            AUTO=1 ;;
    -h|--help)         sed -n '2,18p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown arg: $a"; exit 2 ;;
  esac
done
[ "$AUTO" = "1" ] && PACE="${PACE:-0}"

CANNED="$HERE/canned"
FAILS=0

# ---------------------------------------------------------------------------
# Preflight
# ---------------------------------------------------------------------------
preflight() {
  local missing=0
  [ -n "$ZISKEMU" ] && [ -x "$ZISKEMU" ] || { echo "${C_RED}ziskemu not found${C_RESET} (install via ziskup or set ZISKEMU=)"; missing=1; }
  [ -f "$GUEST_ELF" ] || { echo "${C_RED}guest ELF missing:${C_RESET} $GUEST_ELF — run conformance/build-guest.sh"; missing=1; }
  [ -f "$PACK_PY" ]   || { echo "${C_RED}pack-bytecode.py missing${C_RESET}"; missing=1; }
  command -v "$PYTHON" >/dev/null || { echo "${C_RED}python3 missing${C_RESET}"; missing=1; }
  if [ "$NO_NET" = "0" ] && [ "$MODE" != "check-manifest" ]; then
    command -v cast >/dev/null || { echo "${C_RED}foundry 'cast' missing${C_RESET} (or run with --no-net)"; missing=1; }
  fi
  [ "$missing" = "0" ] || exit 1
}

# Fetch the live block environment (or load canned). Sets *_HEX / *_DEC globals.
fetch_block_env() {
  local json
  if [ "$NO_NET" = "1" ]; then
    json="$(cat "$CANNED/block_env.json")"
    CHAINID_DEC="$(cat "$CANNED/chainid")"
    note "offline mode — using vendored canned block #$(printf '%d' "$(echo "$json" | jq -r .number)")"
  else
    json="$(castr block latest --json)" || { echo "${C_RED}RPC failed${C_RESET} — retry or use --no-net"; exit 1; }
    CHAINID_DEC="$(castr chain-id)" || CHAINID_DEC=1
    echo "$json" > "$WORK/block_env.json"
  fi
  NUMBER_HEX="$(echo "$json" | jq -r .number)"
  TS_HEX="$(echo "$json" | jq -r .timestamp)"
  BASEFEE_HEX="$(echo "$json" | jq -r .baseFeePerGas)"
  COINBASE_HEX="$(echo "$json" | jq -r .miner)"
  BN_DEC="$(printf '%d' "$NUMBER_HEX")"
}

hexdec() { "$PYTHON" -c "import sys; print(int(sys.argv[1],16))" "$1"; }

# ---------------------------------------------------------------------------
# Act 1 — live block environment through verified env opcodes
# ---------------------------------------------------------------------------
act1_env() {
  banner "ACT 1 — A live mainnet block, read by a verified EVM"
  say "We pull the latest block from mainnet and feed its environment into"
  say "evm-asm's environment opcodes — each one a kernel-checked theorem."
  note "block #$BN_DEC  (chain id $CHAINID_DEC)"
  echo
  # name  opcode-byte  env-field  manifest-key  chain-decimal-value
  local rows=(
    "NUMBER|43|number|NUMBER|$BN_DEC"
    "TIMESTAMP|42|timestamp|TIMESTAMP|$(hexdec "$TS_HEX")"
    "BASEFEE|48|base_fee|BASEFEE|$(hexdec "$BASEFEE_HEX")"
    "COINBASE|41|coinbase|COINBASE|$(hexdec "$COINBASE_HEX")"
    "CHAINID|46|chain_id|CHAINID|$CHAINID_DEC"
  )
  local r name op field key want hexval
  for r in "${rows[@]}"; do
    IFS='|' read -r name op field key want <<<"$r"
    case "$name" in
      NUMBER)    hexval="$NUMBER_HEX" ;;
      TIMESTAMP) hexval="$TS_HEX" ;;
      BASEFEE)   hexval="$BASEFEE_HEX" ;;
      COINBASE)  hexval="$COINBASE_HEX" ;;
      CHAINID)   hexval="$(printf '0x%x' "$CHAINID_DEC")" ;;
    esac
    run_guest "act1_$name" "0x$op, 0x00" --env "$field=$hexval"
    assert_dec_eq "$name on the verified guest == mainnet" "$GUEST_WORD_DEC" "$want" || FAILS=$((FAILS+1))
    deep_dive "$key"
  done
  pause
}

# ---------------------------------------------------------------------------
# Act 2 — real transaction calldata through verified arithmetic
# ---------------------------------------------------------------------------
act2_calldata() {
  banner "ACT 2 — Real transaction calldata, through verified arithmetic"
  local calldata
  if [ "$NO_NET" = "1" ]; then
    calldata="$(cat "$CANNED/act2_calldata.hex")"
    note "offline mode — using vendored calldata for tx ${ACT2_TX:0:18}…"
  else
    calldata="$(castr tx "$ACT2_TX" input)" || { echo "${C_RED}RPC failed${C_RESET}"; FAILS=$((FAILS+1)); return; }
    echo "$calldata" > "$WORK/act2_calldata.hex"
  fi
  say "An on-chain ERC-20 transfer. We extract its real 'amount' word with"
  say "CALLDATALOAD and run verified 256-bit arithmetic on it."
  note "tx ${ACT2_TX:0:18}…  selector ${calldata:0:10}"
  # amount word: 32 bytes at calldata offset 0x24 (after 4-byte selector + 32-byte address)
  local off_dec amount_hex amount_dec
  off_dec="$(hexdec "$ACT2_AMOUNT_OFFSET")"
  amount_hex="0x${calldata:$(( 2 + off_dec*2 )):64}"
  amount_dec="$(hexdec "$amount_hex")"
  note "calldata amount word = $amount_dec"
  echo
  # (a) CALLDATALOAD(0x24) == the real amount
  run_guest "act2_load" "0x60, 0x24, 0x35, 0x00" --calldata "$calldata"
  assert_dec_eq "CALLDATALOAD(0x24) on the guest == the tx's real amount" "$GUEST_WORD_DEC" "$amount_dec" || FAILS=$((FAILS+1))
  deep_dive "CALLDATALOAD"
  # (b) verified MUL: amount * 2
  run_guest "act2_mul" "0x60, 0x24, 0x35, 0x60, 0x02, 0x02, 0x00" --calldata "$calldata"
  assert_dec_eq "verified MUL: amount × 2" "$GUEST_WORD_DEC" "$(( amount_dec * 2 ))" || FAILS=$((FAILS+1))
  deep_dive "MUL"
  pause
}

# ---------------------------------------------------------------------------
# Act 3 — real contract bytecode through the verified guest + coverage
# ---------------------------------------------------------------------------
act3_bytecode() {
  banner "ACT 3 — Real on-chain contract bytecode, and the verified frontier"
  local code
  if [ "$NO_NET" = "1" ]; then
    code="$(cat "$CANNED/act3_code.hex")"
    note "offline mode — using vendored $ACT3_NAME bytecode"
  else
    code="$(castr code "$ACT3_CONTRACT")" || { echo "${C_RED}RPC failed${C_RESET}"; FAILS=$((FAILS+1)); return; }
    echo "$code" > "$WORK/act3_code.hex"
  fi
  say "We take $ACT3_NAME's real deployed bytecode and run it through the"
  say "verified guest. Most of it already runs; the rest is the roadmap."
  note "$ACT3_NAME @ ${ACT3_CONTRACT}  (${#code} hex chars)"
  echo
  # Execute the real bytecode (decimals() selector) — show it runs real opcodes.
  local csv
  csv="$(hex_to_csv "$code")"
  run_guest "act3_exec" "$csv" --calldata "0x313ce567"
  note "guest executed real $ACT3_NAME bytecode → halt kind $GUEST_HALT  (see emu log)"
  echo
  say "Opcode-coverage of this real contract against evm-asm's verified set:"
  "$PYTHON" "$HERE/opcode_coverage.py" "$HERE/capabilities.json" "$code"
  note "the 'frontier' opcodes (SLOAD/CALL/…) are exactly the harness roadmap (README)."
  pause
}

closing() {
  banner "What you just saw — and the trust behind it"
  say "Real mainnet data flowed through evm-asm's real RISC-V guest on a zkVM"
  say "emulator, and matched the live chain — backed by kernel-checked proofs."
  echo
  note "Trust base (audited by scripts/check-axioms.sh):"
  note "  • 0 sorry, 0 literal axiom across EvmAsm/"
  note "  • bv_decide & native_decide fully eliminated (no compiler-trust axioms)"
  note "  • only the 3 classical axioms: propext, Classical.choice, Quot.sound"
  echo
  note "Stage 0 of the roadmap: supported-opcode subset over real data."
  note "Next: full opcode coverage → storage/CALL → MPT → whole-block post-state root."
  echo
  if [ "$FAILS" = "0" ]; then
    printf '%s\n' "${C_GREEN}${C_BOLD}All live checks matched the chain.${C_RESET}"
  else
    printf '%s\n' "${C_RED}${C_BOLD}$FAILS check(s) did not match — see output above.${C_RESET}"
  fi
}

# ---------------------------------------------------------------------------
# --report — opcode coverage over a live block's contracts
# ---------------------------------------------------------------------------
report() {
  banner "evm-asm coverage report — real mainnet bytecode"
  fetch_block_env
  note "sampling deployed bytecode of well-known contracts (block #$BN_DEC)"
  echo
  local addr code
  for addr in $REPORT_CONTRACTS; do
    if [ "$NO_NET" = "1" ]; then
      code="$(cat "$CANNED/act3_code.hex")"   # offline: only the vendored one
    else
      code="$(castr code "$addr")" || { note "  $addr: code fetch failed"; continue; }
    fi
    echo "${C_BOLD}$addr${C_RESET}"
    "$PYTHON" "$HERE/opcode_coverage.py" "$HERE/capabilities.json" "$code"
    echo
    [ "$NO_NET" = "1" ] && break
  done
  note "Gap to the next roadmap stage: real SLOAD/SSTORE state, then CALL/CREATE semantics."
}

# ---------------------------------------------------------------------------
# --check-manifest — capabilities.json vs PROGRESS.md
# ---------------------------------------------------------------------------
check_manifest() {
  banner "capability manifest consistency check"
  "$PYTHON" - "$HERE/capabilities.json" "$REPO_ROOT/PROGRESS.md" <<'PY'
import json, re, sys
caps = json.load(open(sys.argv[1]))
prog = open(sys.argv[2]).read()
# PROGRESS.md rows: | <emoji> OP | tier | `witness` | N | notes |
rows = {}
for m in re.finditer(r"^\|\s*[^\sA-Z]*\s*([A-Z0-9.]+(?:\.\.\d+)?)\s*\|\s*(\w+)\s*\|", prog, re.M):
    rows[m.group(1)] = m.group(2)
mismatch = 0
for name, e in caps["opcodes"].items():
    p = rows.get(name)
    if p is None:
        continue  # range/aggregate names may not match 1:1
    if p != e["tier"]:
        print(f"  DRIFT {name}: manifest={e['tier']} PROGRESS.md={p}")
        mismatch += 1
print(f"  checked {len(caps['opcodes'])} manifest opcodes against PROGRESS.md")
print("  OK — no tier drift" if mismatch == 0 else f"  {mismatch} drift(s)")
sys.exit(1 if mismatch else 0)
PY
}

# ---------------------------------------------------------------------------
main() {
  preflight
  case "$MODE" in
    check-manifest) check_manifest ;;
    report)         report ;;
    demo)
      banner "evm-asm — live-chain conformance demo"
      say "A formally-verified EVM, compiled to RISC-V, running real mainnet"
      say "data on a zkVM emulator — and checked against the chain itself."
      note "guest: $(basename "$GUEST_ELF")  (pinned $(cat "$GUEST_DIR/PINNED_COMMIT" 2>/dev/null | cut -c1-9))   emulator: $(basename "$ZISKEMU")"
      pause
      fetch_block_env
      act1_env
      act2_calldata
      act3_bytecode
      closing
      [ "$FAILS" = "0" ] || exit 1
      ;;
  esac
}
main
