#!/usr/bin/env bash
# check-sail-pin.sh — assert the vendored Sail model matches its provenance pin.
#
# `vendor/sail-riscv-zkvm-lean/Out{,.lean}` is machine-extracted from a pinned
# upstream (`riscv/sail-riscv` at the tag recorded in sail-import/PROVENANCE.toml)
# by scripts/regen-sail-model.sh. It is a TRUST ANCHOR: every SailEquiv theorem is
# a statement about *that* model, so a hand-edit there silently changes what those
# theorems mean. The files carry no "generated" header and are plain checked-in
# blobs, so nothing else in the tree prevents that.
#
# This gate is the backstop PROVENANCE.toml has always promised (it and
# regen-sail-model.sh --plan both reference this script by name). It recomputes
# the two pinned digests and fails on any drift.
#
# Usage:
#   scripts/check-sail-pin.sh            # verify (default; CI mode)
#   scripts/check-sail-pin.sh --check    # same
#   scripts/check-sail-pin.sh --write    # recompute and rewrite the pins
#
# `--write` is for the ONE legitimate case: you have just re-run
# scripts/regen-sail-model.sh and re-vendored its output. It rewrites
# model_sha256/config_sha256 in place; the accompanying tag/version/module fields
# are yours to update by hand, and the diff is the reviewer's signal.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PROVENANCE="sail-import/PROVENANCE.toml"
VENDOR_DIR="vendor/sail-riscv-zkvm-lean"
# Resolved from PROVENANCE's own `config_file` field rather than hardcoded here —
# a hardcoded copy silently kept hashing the OLD config after a regen changed the
# recorded one, making config_sha256 a pin on the wrong file. One source of truth.
CONFIG_FILE="$(grep -m1 -E '^[[:space:]]*config_file[[:space:]]*=' "$PROVENANCE" | sed -E 's/.*=[[:space:]]*"([^"]+)".*/\1/')"
[[ -n "$CONFIG_FILE" ]] || { echo "check-sail-pin: could not read config_file from $PROVENANCE" >&2; exit 1; }

mode="check"
case "${1:-}" in
  ""|--check) mode="check" ;;
  --write)    mode="write" ;;
  *) echo "usage: $0 [--check | --write]" >&2; exit 2 ;;
esac

for p in "$PROVENANCE" "$CONFIG_FILE" "$VENDOR_DIR"; do
  [[ -e "$p" ]] || { echo "check-sail-pin: missing $p" >&2; exit 1; }
done

# Portable sha256 — selected by OUTPUT FORMAT, not by command name.
#
# The pinned digest is a hash *of the hash listing*, so the listing's format is
# load-bearing. GNU coreutils emits "<hash>  <path>"; BSD emits
# "SHA256 (<path>) = <hash>". These give different digests-of-digests.
#
# Name-based detection is a trap here: macOS ships /sbin/sha256sum, which despite
# the GNU name emits the BSD form, while its `shasum -a 256` emits the GNU form.
# So probe each candidate and keep the first that produces the GNU layout.
# (Same family as the BSD-vs-GNU mktemp issue that makes check-axioms.sh fail
# locally — worth not repeating.)
SHA_BIN=""
for cand in "sha256sum" "shasum -a 256" "gsha256sum"; do
  # shellcheck disable=SC2086
  command -v ${cand%% *} >/dev/null 2>&1 || continue
  if printf '' | $cand - 2>/dev/null | grep -qE '^[0-9a-f]{64}  '; then
    SHA_BIN="$cand"; break
  fi
done
if [[ -z "$SHA_BIN" ]]; then
  echo "check-sail-pin: no GNU-format sha256 tool found (tried sha256sum, shasum -a 256, gsha256sum)." >&2
  echo "  The pin is a hash of a '<hash>  <path>' listing; a BSD-format tool yields a different digest." >&2
  exit 1
fi

# The recipe below is pinned verbatim by PROVENANCE.toml ("check-sail-pin.sh (P6)
# must use this exact invocation"). Three things are load-bearing and must not be
# "tidied": CWD is the vendor dir so paths render as './…'; LC_ALL=C makes the sort
# locale-stable; './.lake/*' is excluded so build artifacts do not perturb the hash
# (a gate that fires on a clean checkout after a build is a gate that gets disabled).
#
# SCOPE: `.lean` only, matching the pinned recipe. The other tracked files in the
# vendor dir are deliberately out: `lakefile.toml` and `lean-toolchain` are
# hand-owned (the regen does not emit them), and `.gitignore`/`LICENSE` are inert.
# The one trust-relevant item among them — the lean-sail runtime rev that
# `lakefile.toml` git-pins — is covered separately by check_lean_sail_rev below,
# since the model `import Sail.Sail`s it and a silent bump would change the
# runtime under every theorem.
#
# `-print0 | sort -z | xargs -0` hardens against whitespace in filenames. Verified
# to produce a byte-identical digest to the pinned recipe. NOTE on ARG_MAX: if
# xargs splits into several invocations the digest is unchanged, because GNU-format
# output is one line per file and order is preserved across the splits — so the
# concatenation the outer hash sees is the same.
compute_model_hash() {
  # shellcheck disable=SC2086
  ( cd "$VENDOR_DIR" && \
    find . -name '*.lean' -not -path './.lake/*' -print0 | LC_ALL=C sort -z \
      | xargs -0 $SHA_BIN | $SHA_BIN ) \
    | awk '{print $1}'
}

# The vendored model imports the EXTERNAL lean-sail runtime, whose rev is git-pinned
# by the vendor lakefile — a file outside model_sha256's `.lean` scope. PROVENANCE
# records the intended rev; assert the two still agree so the runtime cannot be
# bumped without the provenance record moving with it.
check_lean_sail_rev() {
  local lakefile="$VENDOR_DIR/lakefile.toml"
  [[ -f "$lakefile" ]] || return 0
  local in_lakefile in_provenance
  in_lakefile="$(grep -m1 -E '^[[:space:]]*rev[[:space:]]*=' "$lakefile" \
    | sed -E 's/.*=[[:space:]]*"([0-9a-f]{40})".*/\1/')"
  in_provenance="$(grep -m1 -E '^[[:space:]]*lean_sail_rev[[:space:]]*=[[:space:]]*"[0-9a-f]{40}"' "$PROVENANCE" \
    | sed -E 's/.*"([0-9a-f]{40})".*/\1/')"
  if [[ -n "$in_lakefile" && -n "$in_provenance" && "$in_lakefile" != "$in_provenance" ]]; then
    cat >&2 <<EOF
check-sail-pin: FAIL — vendored lean-sail runtime rev does not match its pin.
  lakefile   ($lakefile): $in_lakefile
  provenance (lean_sail_rev):                          $in_provenance
The extracted model imports this runtime, so bumping it changes the semantics
underneath every SailEquiv theorem. Update PROVENANCE.toml in the same commit.
EOF
    return 1
  fi
  return 0
}

compute_config_hash() {
  # shellcheck disable=SC2086
  $SHA_BIN "$CONFIG_FILE" | awk '{print $1}'
}

pinned_of() {
  # First `key = "value"` in the file; the [current]/[target] blocks agree.
  grep -m1 -E "^[[:space:]]*$1[[:space:]]*=" "$PROVENANCE" \
    | sed -E 's/.*=[[:space:]]*"([0-9a-f]{64})".*/\1/'
}

actual_model="$(compute_model_hash)"
actual_config="$(compute_config_hash)"
pinned_model="$(pinned_of model_sha256)"
pinned_config="$(pinned_of config_sha256)"

if [[ "$mode" == "write" ]]; then
  tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
  sed -E "s/^([[:space:]]*model_sha256[[:space:]]*=[[:space:]]*\")[0-9a-f]{64}(\")/\1${actual_model}\2/; \
          s/^([[:space:]]*config_sha256[[:space:]]*=[[:space:]]*\")[0-9a-f]{64}(\")/\1${actual_config}\2/" \
    "$PROVENANCE" > "$tmp"
  mv "$tmp" "$PROVENANCE"; trap - EXIT
  echo "check-sail-pin: wrote model_sha256=${actual_model}"
  echo "check-sail-pin: wrote config_sha256=${actual_config}"
  echo "check-sail-pin: NOTE — update the tag / sail_version / sail_modules fields by hand if the regen changed them."
  exit 0
fi

fail=0
if [[ "$actual_model" != "$pinned_model" ]]; then
  cat >&2 <<EOF
check-sail-pin: FAIL — vendored Sail model does not match its pin.
  pinned (sail-import/PROVENANCE.toml model_sha256): $pinned_model
  actual ($VENDOR_DIR):                              $actual_model

The vendored model is a trust anchor: every EvmAsm/Rv64/SailEquiv theorem is a
statement about the pinned extraction. If you hand-edited a file under
$VENDOR_DIR, revert it — patch the Sail source upstream or widen the extraction
scope and re-run scripts/regen-sail-model.sh instead.
If you DID regenerate and re-vendor deliberately, re-pin with:
  scripts/check-sail-pin.sh --write
and update the tag / sail_version / sail_modules fields in the same commit.
EOF
  fail=1
fi

if [[ "$actual_config" != "$pinned_config" ]]; then
  cat >&2 <<EOF
check-sail-pin: FAIL — Sail extraction config does not match its pin.
  pinned (config_sha256): $pinned_config
  actual ($CONFIG_FILE):  $actual_config
Changing the config changes which extensions the extracted model reports as
supported, so it must be accompanied by a regen. Re-pin with --write.
EOF
  fail=1
fi

check_lean_sail_rev || fail=1

if (( fail )); then exit 1; fi

echo "check-sail-pin: OK — vendored model, config and lean-sail rev match sail-import/PROVENANCE.toml."
