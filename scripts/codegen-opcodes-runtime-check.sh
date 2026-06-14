#!/usr/bin/env bash
# codegen-opcodes-runtime-check.sh — M8.5 runtime-bytecode test runner.
#
# Builds the M8.5 `runtime_dispatcher` ELF **once**, then iterates
# Lean-declared test cases (`EvmAsm/Codegen/Tests/Cases.lean`) packing
# each per-case bytecode into a ziskemu `-i <file>` payload and reusing
# the same dispatcher ELF.
#
# Replaces the per-case-ELF assemble + link work that
# `scripts/codegen-opcodes-check.sh` does for every case. Same expected
# outputs; ~6× faster on the macOS dev box.
#
# Adding a new opcode regression = appending one record to
# `opcodeTestCases` in `Tests/Cases.lean` — no edits to this script.
#
# Exit:
#   0 — all cases match expected
#   1 — emission / build / emulation failed, or any output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found — install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

PYTHON="${PYTHON:-python3}"
if ! command -v "$PYTHON" >/dev/null 2>&1; then
  echo "$PYTHON not found — set PYTHON=... or install python3" >&2
  exit 1
fi

OPCODE_RUNTIME_STEP_LIMIT="${OPCODE_RUNTIME_STEP_LIMIT:-5000000}"

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit + link runtime_dispatcher.elf (once)"
lake exe codegen --program runtime_dispatcher --halt linux93 -o gen-out/runtime_dispatcher

# `--list-test-cases` is an optional-field TSV:
#   <name> <expected_hex> <bytecode_csv> <calldata> <storage> ...
# M21 adds calldata; M22 adds storage preload; later columns carry
# optional output-surface assertions.
# Single source of truth lives in `EvmAsm/Codegen/Tests/Cases.lean`.
LIST_FILE="gen-out/.opcodes-list"
lake exe codegen --list-test-cases >"$LIST_FILE"

TOTAL=0
while IFS= read -r _; do TOTAL=$((TOTAL + 1)); done <"$LIST_FILE"

if [[ "$TOTAL" -eq 0 ]]; then
  echo "==> no test cases declared in opcodeTestCases" >&2
  exit 1
fi

echo "==> running $TOTAL test case(s) through runtime_dispatcher.elf"

FAILED=()
while IFS= read -r line; do
  # POSIX `read -r` with IFS=$'\t' collapses adjacent tab separators
  # (tab is treated as IFS-whitespace), which silently shifts the
  # storage column into the calldata slot when calldata is empty.
  # `cut -f` preserves empty fields, so we slice each column
  # explicitly. Order matches `--list-test-cases` 21-column TSV
  # (M23 added halt-kind; M24 added log lengths; M25 added post-state
  # slot dumps; M26 added receipt event-log capture; M31 added the
  # extended RETURN/REVERT returndata surface).
  name=$(printf '%s' "$line" | cut -f1)
  expected=$(printf '%s' "$line" | cut -f2)
  bytecode_csv=$(printf '%s' "$line" | cut -f3)
  calldata=$(printf '%s' "$line" | cut -f4)
  storage=$(printf '%s' "$line" | cut -f5)
  blob_base_fee=$(printf '%s' "$line" | cut -f6)
  blob_hashes=$(printf '%s' "$line" | cut -f7)
  block_number=$(printf '%s' "$line" | cut -f8)
  block_hashes=$(printf '%s' "$line" | cut -f9)
  env=$(printf '%s' "$line" | cut -f10)
  expected_halt_kind=$(printf '%s' "$line" | cut -f11)
  expected_persistent_log_length=$(printf '%s' "$line" | cut -f12)
  expected_transient_log_length=$(printf '%s' "$line" | cut -f13)
  expected_post_storage=$(printf '%s' "$line" | cut -f14)
  expected_event_log_count=$(printf '%s' "$line" | cut -f15)
  expected_event_log_first=$(printf '%s' "$line" | cut -f16)
  gas_limit=$(printf '%s' "$line" | cut -f17)
  expected_return_data_copied=$(printf '%s' "$line" | cut -f18)
  expected_return_data_length=$(printf '%s' "$line" | cut -f19)
  expected_return_data_hex=$(printf '%s' "$line" | cut -f20)
  expected_selfdestruct_beneficiary=$(printf '%s' "$line" | cut -f21)

  if [[ -z "$name" || -z "$expected" || -z "$bytecode_csv" ]]; then
    echo
    echo "==> SKIP: malformed --list-test-cases line (missing 1+ columns)"
    FAILED+=("${name:-<unknown>} (malformed-tsv)")
    continue
  fi

  echo
  echo "==> pack $name"
  # M21/M22: pass --calldata / --storage only when non-empty so pre-M21
  # / pre-M22 invocations produce identical input bytes downstream
  # (zero-length segments still get appended by pack-bytecode.py).
  # `${arr[@]+...}` guards against `set -u` complaining about an
  # empty-array expansion on macOS bash 3.2.
  pack_args=()
  if [[ -n "${calldata:-}" ]]; then
    pack_args+=(--calldata "$calldata")
  fi
  if [[ -n "${storage:-}" ]]; then
    pack_args+=(--storage "$storage")
  fi
  if [[ -n "${blob_base_fee:-}" ]]; then
    pack_args+=(--blob-base-fee "$blob_base_fee")
  fi
  if [[ -n "${blob_hashes:-}" ]]; then
    pack_args+=(--blob-hashes "$blob_hashes")
  fi
  if [[ -n "${block_number:-}" ]]; then
    pack_args+=(--block-number "$block_number")
  fi
  if [[ -n "${block_hashes:-}" ]]; then
    pack_args+=(--block-hashes "$block_hashes")
  fi
  if [[ -n "${env:-}" ]]; then
    pack_args+=(--env "$env")
  fi
  if [[ -n "${gas_limit:-}" ]]; then
    pack_args+=(--gas "$gas_limit")
  fi
  "$PYTHON" scripts/pack-bytecode.py ${pack_args[@]+"${pack_args[@]}"} "$bytecode_csv" "gen-out/$name.input"

  echo "==> ziskemu -e runtime_dispatcher.elf -i gen-out/$name.input"
  : >"gen-out/$name.output"
  set +e
  "$ZISKEMU" -e gen-out/runtime_dispatcher.elf -i "gen-out/$name.input" \
    -o "gen-out/$name.output" -n "$OPCODE_RUNTIME_STEP_LIMIT" \
    >"gen-out/$name.emu.log" 2>&1
  emu_status=$?
  set -e

  case_failed=""
  if [[ "$emu_status" -ne 0 ]]; then
    case_failed="emulator_exit_$emu_status"
  fi

  if [[ -f "gen-out/$name.output" ]]; then
    actual="$(xxd -p -c 64 -l 32 "gen-out/$name.output" | tr -d '\n')"
  else
    actual=""
    case_failed="${case_failed:+$case_failed,}output_missing"
  fi

  echo "expected:"
  echo "  $expected"
  echo "actual:"
  echo "  $actual"

  if [[ "$actual" != "$expected" ]]; then
    case_failed="${case_failed:+$case_failed,}output"
  fi

  # M23: if the case asserts on halt-kind, read OUTPUT_ADDR + 32..40
  # (8 LE bytes) and compare. Empty field = skip (back-compat).
  if [[ -n "${expected_halt_kind:-}" ]]; then
    actual_halt_kind="$(xxd -p -c 64 -s 32 -l 8 "gen-out/$name.output" | tr -d '\n')"
    echo "expected halt_kind:"
    echo "  $expected_halt_kind"
    echo "actual halt_kind:"
    echo "  $actual_halt_kind"
    if [[ "$actual_halt_kind" != "$expected_halt_kind" ]]; then
      case_failed="${case_failed:+$case_failed,}halt_kind"
    fi
  fi

  # M24: persistent log_length at OUTPUT+40..48
  if [[ -n "${expected_persistent_log_length:-}" ]]; then
    actual_persistent="$(xxd -p -c 64 -s 40 -l 8 "gen-out/$name.output" | tr -d '\n')"
    echo "expected persistent_log_length:"
    echo "  $expected_persistent_log_length"
    echo "actual persistent_log_length:"
    echo "  $actual_persistent"
    if [[ "$actual_persistent" != "$expected_persistent_log_length" ]]; then
      case_failed="${case_failed:+$case_failed,}persistent_log_length"
    fi
  fi

  # M24: transient log_length at OUTPUT+48..56
  if [[ -n "${expected_transient_log_length:-}" ]]; then
    actual_transient="$(xxd -p -c 64 -s 48 -l 8 "gen-out/$name.output" | tr -d '\n')"
    echo "expected transient_log_length:"
    echo "  $expected_transient_log_length"
    echo "actual transient_log_length:"
    echo "  $actual_transient"
    if [[ "$actual_transient" != "$expected_transient_log_length" ]]; then
      case_failed="${case_failed:+$case_failed,}transient_log_length"
    fi
  fi

  # M25: post-state slot data at OUTPUT+56..
  # Field length is variable (8-byte count + N × 64-byte slot entries).
  # Read exactly `len(expected)/2` bytes from offset 56 and compare.
  if [[ -n "${expected_post_storage:-}" ]]; then
    post_len_bytes=$(( ${#expected_post_storage} / 2 ))
    actual_post_storage="$(xxd -p -c 256 -s 56 -l "$post_len_bytes" "gen-out/$name.output" | tr -d '\n')"
    echo "expected post_storage:"
    echo "  $expected_post_storage"
    echo "actual post_storage:"
    echo "  $actual_post_storage"
    if [[ "$actual_post_storage" != "$expected_post_storage" ]]; then
      case_failed="${case_failed:+$case_failed,}post_storage"
    fi
  fi

  # M26: receipt event LOG count at OUTPUT+56. This shares the M25
  # storage diagnostic window; cases should assert one or the other.
  if [[ -n "${expected_event_log_count:-}" ]]; then
    actual_event_log_count="$(xxd -p -c 64 -s 56 -l 8 "gen-out/$name.output" | tr -d '\n')"
    echo "expected event_log_count:"
    echo "  $expected_event_log_count"
    echo "actual event_log_count:"
    echo "  $actual_event_log_count"
    if [[ "$actual_event_log_count" != "$expected_event_log_count" ]]; then
      case_failed="${case_failed:+$case_failed,}event_log_count"
    fi
  fi

  # M26: first event descriptor prefix at OUTPUT+64. Field length is
  # variable so each case can assert just the meaningful prefix.
  if [[ -n "${expected_event_log_first:-}" ]]; then
    event_first_len_bytes=$(( ${#expected_event_log_first} / 2 ))
    actual_event_log_first="$(xxd -p -c 512 -s 64 -l "$event_first_len_bytes" "gen-out/$name.output" | tr -d '\n')"
    echo "expected event_log_first:"
    echo "  $expected_event_log_first"
    echo "actual event_log_first:"
    echo "  $actual_event_log_first"
    if [[ "$actual_event_log_first" != "$expected_event_log_first" ]]; then
      case_failed="${case_failed:+$case_failed,}event_log_first"
    fi
  fi

  # M31: extended RETURN/REVERT returndata diagnostics. The legacy
  # OUTPUT[0..32] prefix and halt_kind at OUTPUT+32 remain unchanged;
  # these fields assert the wider 256-byte ziskemu output surface.
  if [[ -n "${expected_return_data_copied:-}" ]]; then
    actual_return_data_copied="$(xxd -p -c 64 -s 248 -l 8 "gen-out/$name.output" | tr -d '\n')"
    echo "expected return_data_copied:"
    echo "  $expected_return_data_copied"
    echo "actual return_data_copied:"
    echo "  $actual_return_data_copied"
    if [[ "$actual_return_data_copied" != "$expected_return_data_copied" ]]; then
      case_failed="${case_failed:+$case_failed,}return_data_copied"
    fi
  fi

  if [[ -n "${expected_return_data_length:-}" ]]; then
    actual_return_data_length="$(xxd -p -c 64 -s 64 -l 8 "gen-out/$name.output" | tr -d '\n')"
    echo "expected return_data_length:"
    echo "  $expected_return_data_length"
    echo "actual return_data_length:"
    echo "  $actual_return_data_length"
    if [[ "$actual_return_data_length" != "$expected_return_data_length" ]]; then
      case_failed="${case_failed:+$case_failed,}return_data_length"
    fi
  fi

  if [[ -n "${expected_return_data_hex:-}" ]]; then
    return_data_len_bytes=$(( ${#expected_return_data_hex} / 2 ))
    actual_return_data_hex="$(xxd -p -c 512 -s 72 -l "$return_data_len_bytes" "gen-out/$name.output" | tr -d '\n')"
    echo "expected return_data_hex:"
    echo "  $expected_return_data_hex"
    echo "actual return_data_hex:"
    echo "  $actual_return_data_hex"
    if [[ "$actual_return_data_hex" != "$expected_return_data_hex" ]]; then
      case_failed="${case_failed:+$case_failed,}return_data_hex"
    fi
  fi

  # SELFDESTRUCT staged-beneficiary diagnostic at OUTPUT+56. This shares the
  # storage/event diagnostic window, so only SELFDESTRUCT staging cases should
  # set this field.
  if [[ -n "${expected_selfdestruct_beneficiary:-}" ]]; then
    selfdestruct_beneficiary_len_bytes=$(( ${#expected_selfdestruct_beneficiary} / 2 ))
    actual_selfdestruct_beneficiary="$(xxd -p -c 64 -s 56 -l "$selfdestruct_beneficiary_len_bytes" "gen-out/$name.output" | tr -d '\n')"
    echo "expected selfdestruct_beneficiary:"
    echo "  $expected_selfdestruct_beneficiary"
    echo "actual selfdestruct_beneficiary:"
    echo "  $actual_selfdestruct_beneficiary"
    if [[ "$actual_selfdestruct_beneficiary" != "$expected_selfdestruct_beneficiary" ]]; then
      case_failed="${case_failed:+$case_failed,}selfdestruct_beneficiary"
    fi
  fi

  if [[ -z "$case_failed" ]]; then
    echo "==> PASS: $name"
  else
    echo "==> FAIL: $name mismatch ($case_failed)"
    FAILED+=("$name ($case_failed)")
  fi
done <"$LIST_FILE"

echo
if [[ ${#FAILED[@]} -eq 0 ]]; then
  echo "==> ALL PASS ($TOTAL case(s))"
  exit 0
else
  echo "==> FAIL: ${#FAILED[@]} of $TOTAL case(s) failed:"
  for f in "${FAILED[@]}"; do
    echo "    - $f"
  done
  exit 1
fi
