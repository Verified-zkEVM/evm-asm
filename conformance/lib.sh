#!/usr/bin/env bash
# conformance/lib.sh — shared helpers for the evm-asm live-chain conformance
# harness. Sourced by run.sh and build-guest.sh. No side effects on source.
#
# The harness runs REAL Ethereum data (block environment, transaction calldata,
# contract bytecode) through the actual verified evm-asm RISC-V guest on the
# Zisk emulator, and cross-checks the result against the live chain. See
# conformance/README.md for scope, honesty caveats, and the maturity roadmap.

# ---------------------------------------------------------------------------
# Paths and tool resolution
# ---------------------------------------------------------------------------
CONF_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$CONF_DIR/.." && pwd)"
GUEST_DIR="$CONF_DIR/guest"

# Vendored, prebuilt guest artifacts (see build-guest.sh for provenance).
GUEST_ELF="${GUEST_ELF:-$GUEST_DIR/runtime_dispatcher.elf}"
PACK_PY="${PACK_PY:-$GUEST_DIR/pack-bytecode.py}"
# Fall back to the repo's live packer if the vendored one is absent.
[ -f "$PACK_PY" ] || PACK_PY="$REPO_ROOT/scripts/pack-bytecode.py"

PYTHON="${PYTHON:-python3}"
ZISKEMU="${ZISKEMU:-}"
if [ -z "$ZISKEMU" ]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [ -x "$HOME/.zisk/bin/ziskemu" ]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  fi
fi

# Public mainnet RPC (no key). Override with RPC_URL=...; FALLBACK list is tried
# in order on failure (the free endpoints rate-limit bursts).
RPC_URL="${RPC_URL:-https://ethereum-rpc.publicnode.com}"
RPC_FALLBACKS=(
  "https://ethereum-rpc.publicnode.com"
  "https://eth.llamarpc.com"
  "https://rpc.ankr.com/eth"
  "https://cloudflare-eth.com"
)
export FOUNDRY_DISABLE_NIGHTLY_WARNING=1

WORK="${WORK:-$REPO_ROOT/gen-out/conformance}"
mkdir -p "$WORK"

# ---------------------------------------------------------------------------
# Presentation
# ---------------------------------------------------------------------------
if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
  C_RESET=$'\033[0m'; C_DIM=$'\033[2m'; C_BOLD=$'\033[1m'
  C_GREEN=$'\033[32m'; C_RED=$'\033[31m'; C_CYAN=$'\033[36m'
  C_YEL=$'\033[33m'; C_MAG=$'\033[35m'
else
  C_RESET=; C_DIM=; C_BOLD=; C_GREEN=; C_RED=; C_CYAN=; C_YEL=; C_MAG=
fi

# Narration. PACE controls typewriter speed; set PACE=0 to disable.
PACE="${PACE:-0.012}"
say() {
  local line="$*"
  if [ "$PACE" = "0" ] || [ ! -t 1 ]; then printf '%s\n' "$line"; return; fi
  local i ch
  for (( i=0; i<${#line}; i++ )); do ch="${line:$i:1}"; printf '%s' "$ch"; sleep "$PACE"; done
  printf '\n'
}
rule()    { printf '%s\n' "${C_DIM}────────────────────────────────────────────────────────────────${C_RESET}"; }
banner()  { printf '\n%s\n' "${C_BOLD}${C_MAG}$*${C_RESET}"; rule; }
note()    { printf '%s\n' "${C_DIM}$*${C_RESET}"; }
pause()   { [ "${AUTO:-0}" = "1" ] && return; [ -t 0 ] || return; printf '%s' "${C_DIM}  (enter to continue)${C_RESET}"; read -r _; }

# ---------------------------------------------------------------------------
# RPC (Foundry cast) with retry + fallback
# ---------------------------------------------------------------------------
# Usage: castr <cast-subcommand> [args...]   — appends --rpc-url, retries.
castr() {
  local urls=("$RPC_URL") u out rc
  for u in "${RPC_FALLBACKS[@]}"; do [ "$u" = "$RPC_URL" ] || urls+=("$u"); done
  local attempt
  for attempt in 1 2 3; do
    for u in "${urls[@]}"; do
      if out="$(cast "$@" --rpc-url "$u" 2>/dev/null)" && [ -n "$out" ]; then
        printf '%s' "$out"; return 0
      fi
    done
  done
  return 1
}

# ---------------------------------------------------------------------------
# Bytecode / value helpers
# ---------------------------------------------------------------------------
# "0x6042..." (or "6042...") -> "0x60, 0x42, ..." CSV that pack-bytecode.py reads.
hex_to_csv() {
  local h="$1"; h="${h#0x}"; h="${h#0X}"
  "$PYTHON" - "$h" <<'PY'
import sys
h = sys.argv[1].strip()
if len(h) % 2: h = "0" + h
print(", ".join("0x%s" % h[i:i+2] for i in range(0, len(h), 2)) or "0x00")
PY
}

# Read a packed ziskemu OUTPUT file's top 32-byte word (little-endian stack
# representation) as a decimal integer.
out_word_dec() {
  local f="$1"
  "$PYTHON" - "$f" <<'PY'
import sys
data = open(sys.argv[1], "rb").read()
w = data[:32].ljust(32, b"\x00")
print(int.from_bytes(w, "little"))
PY
}

# Halt kind at OUTPUT+32 (0 STOP/RETURN, 2 REVERT, 3 INVALID, ...).
out_halt_kind() {
  local f="$1"
  "$PYTHON" - "$f" <<'PY'
import sys
data = open(sys.argv[1], "rb").read()
print(int.from_bytes(data[32:40].ljust(8, b"\x00"), "little"))
PY
}

# ---------------------------------------------------------------------------
# The core pipeline: bytecode (+ optional pack args) -> verified guest -> result
# ---------------------------------------------------------------------------
# Usage: run_guest <name> <bytecode_csv> [extra pack-bytecode.py args...]
# Sets globals: GUEST_OUT_FILE, GUEST_WORD_DEC, GUEST_HALT
run_guest() {
  local name="$1"; shift
  local bytecode_csv="$1"; shift
  local infile="$WORK/$name.input"
  local outfile="$WORK/$name.output"
  "$PYTHON" "$PACK_PY" "$@" "$bytecode_csv" "$infile" >/dev/null
  "$ZISKEMU" -e "$GUEST_ELF" -i "$infile" -o "$outfile" -n 500000 \
    >"$WORK/$name.emu.log" 2>&1
  GUEST_OUT_FILE="$outfile"
  GUEST_WORD_DEC="$(out_word_dec "$outfile")"
  GUEST_HALT="$(out_halt_kind "$outfile")"
}

# Compare two decimal strings; prints a PASS/FAIL headline. Returns 0/1.
# Usage: assert_dec_eq "<headline>" <guest_dec> <chain_dec>
assert_dec_eq() {
  local headline="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    printf '%s %s\n' "${C_GREEN}${C_BOLD}✓ MATCH${C_RESET}" "$headline"
    printf '   %sverified guest = %s   chain = %s%s\n' "$C_DIM" "$got" "$want" "$C_RESET"
    return 0
  else
    printf '%s %s\n' "${C_RED}${C_BOLD}✗ MISMATCH${C_RESET}" "$headline"
    printf '   %sverified guest = %s   chain = %s%s\n' "$C_DIM" "$got" "$want" "$C_RESET"
    return 1
  fi
}

# Proof deep-dive: show an opcode's tier, witness theorem, and cycle bound from
# the capability manifest. Only printed when DEEP=1.
deep_dive() {
  [ "${DEEP:-0}" = "1" ] || return 0
  local op="$1"
  "$PYTHON" - "$CONF_DIR/capabilities.json" "$op" <<'PY'
import json, sys
caps = json.load(open(sys.argv[1]))
op = sys.argv[2]
e = caps["opcodes"].get(op)
if not e:
    print("   (no manifest entry for %s)" % op); sys.exit(0)
tier = e["tier"]; w = e.get("witness"); c = e.get("cycles")
mark = {"proven":"✅ proven","conditional":"🔶 conditional","partial":"🟡 partial",
        "execSpec":"⏳ execSpec","notStarted":"✗ notStarted"}.get(tier, tier)
print("   ┌ %s  (byte %s)  —  %s" % (op, e["byte"], mark))
if w:  print("   │ kernel-checked theorem: %s" % w)
if c is not None: print("   │ verified cycle bound:   cpsTripleWithin %s" % c)
print("   └ defined in EvmAsm/Evm64/  (no sorry, no axiom beyond the 3 classical)")
PY
}

# Load the proven-tier opcode set into PROVEN_OPS (assoc array of byte->name).
manifest_byte_tier() {
  "$PYTHON" - "$CONF_DIR/capabilities.json" <<'PY'
import json, sys
caps = json.load(open(sys.argv[1]))
for name, e in caps["opcodes"].items():
    b = e["byte"]
    # Expand range entries (PUSH2..32 etc.) to individual byte rows.
    if "-" in b:
        lo, hi = (int(x, 16) for x in b.split("-"))
        for v in range(lo, hi + 1):
            print("0x%02x\t%s\t%s\t%s" % (v, name, e["tier"], e.get("runtime")))
    else:
        print("%s\t%s\t%s\t%s" % (b, name, e["tier"], e.get("runtime")))
PY
}
