#!/usr/bin/env bash
# Emit/link smoke for the EEST verdict-debug probe.
#
# This intentionally does not run fixtures. It protects the diagnostic path that
# codegen-eest-stateless-check.sh uses after succ mismatches: normal codegen ELF
# emission, plus the experimental --asm-only BSR-cap patch/assemble/link path.
set -euo pipefail

cd "$(dirname "$0")/.."

OUT_DIR="${VERDICT_DEBUG_SMOKE_OUT_DIR:-gen-out/verdict-debug-smoke}"
NORMAL_PREFIX="$OUT_DIR/zisk_stateless_verdict_v2_normal"
PATCHED_PREFIX="$OUT_DIR/zisk_stateless_verdict_v2_patched"
BSR_WITNESS_CAP="${EEST_BSR_WITNESS_CAP:-262144}"
BSR_BAL_CAP="${EEST_BSR_BAL_CAP:-1024}"

resolve_riscv_tool() {
  local env_var="$1"
  shift
  local from_env="${!env_var:-}"
  local candidate
  if [[ -n "$from_env" ]]; then
    echo "$from_env"
    return 0
  fi
  for candidate in "$@"; do
    if command -v "$candidate" >/dev/null 2>&1; then
      command -v "$candidate"
      return 0
    fi
  done
  echo "$1"
}

patch_bsr_caps_asm() {
  local asm="$1"
  local old_witness="  la t0, bsr_fail_code; sd zero, 0(t0); li t1, 524288; bgtu a2, t1, .Lbsr_cons_change_cap"
  local new_witness="  la t0, bsr_fail_code; sd zero, 0(t0); li t1, $BSR_WITNESS_CAP; bgtu a2, t1, .Lbsr_cons_change_cap"
  local old_bal=$'  li t0, 2000; divu t1, a0, t0\n  la t2, bsr_bal_count; ld t6, 0(t2); bgtu t6, t1, .Lbsr_cons_change_cap; add t0, s1, t6; li t1, 100018; bgtu t0, t1, .Lbsr_cons_change_cap'
  local new_bal=$'  li t0, 2000; divu t1, a0, t0\n  la t2, bsr_bal_count; ld t6, 0(t2); bgtu t6, t1, .Lbsr_cons_change_cap; li t1, '"$BSR_BAL_CAP"$'; bgtu t6, t1, .Lbsr_cons_change_cap; add t0, s1, t6; li t1, 100018; bgtu t0, t1, .Lbsr_cons_change_cap'

  python3 - "$asm" "$old_witness" "$new_witness" "$old_bal" "$new_bal" <<'PYPATCH'
import sys

path, old_witness, new_witness, old_bal, new_bal = sys.argv[1:]
text = open(path, "r", encoding="utf-8").read()
for label, old, new in (
    ("block_state_root witness-cap", old_witness, new_witness),
    ("block_state_root BAL row-cap", old_bal, new_bal),
):
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one {label} instruction, found {count}")
    text = text.replace(old, new, 1)
open(path, "w", encoding="utf-8").write(text)
PYPATCH
}

check_formatter_reaches_final_word() {
  python3 - <<'PYCHECK'
import re
from pathlib import Path

prologue = Path("EvmAsm/Codegen/Programs/BlockVerdict.lean").read_text()
formatter = Path("scripts/codegen-eest-stateless-check.sh").read_text()
offsets = [int(m.group(1)) for m in re.finditer(r"sd t2, (\d+)\(t0\)", prologue)]
if not offsets:
    raise SystemExit("no verdict-debug OUTPUT stores found")
last_offset = max(offsets)
required_size = last_offset + 8
if f'-ge {required_size}' not in formatter:
    raise SystemExit(
        f"formatter does not gate on final verdict-debug size {required_size}"
    )
if "wlh_linear_max_section_len" not in formatter:
    raise SystemExit("formatter is missing the final witness lookup labels")
print(f"==> verdict-debug formatter reaches final word: offset={last_offset} size={required_size}")
PYCHECK
}

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

echo "==> emit/link normal zisk_stateless_verdict_v2 debug probe"
lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o "$NORMAL_PREFIX" >/dev/null
test -s "$NORMAL_PREFIX.elf"

echo "==> emit/patch/assemble/link experimental zisk_stateless_verdict_v2 debug probe"
lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o "$PATCHED_PREFIX" --asm-only >/dev/null
patch_bsr_caps_asm "$PATCHED_PREFIX.s"
as_tool="$(resolve_riscv_tool RISCV_AS riscv64-unknown-elf-as riscv64-elf-as)"
ld_tool="$(resolve_riscv_tool RISCV_LD riscv64-unknown-elf-ld riscv64-elf-ld)"
"$as_tool" -march=rv64imac -mno-relax -o "$PATCHED_PREFIX.o" "$PATCHED_PREFIX.s"
"$ld_tool" -Ttext=0x80000000 -Tdata=0xa3000000 \
  --section-start=.bss=0xa4000000 \
  --section-start=.sszscratch=0xbf600000 \
  -nostdlib --no-relax -o "$PATCHED_PREFIX.elf" "$PATCHED_PREFIX.o"
test -s "$PATCHED_PREFIX.elf"

check_formatter_reaches_final_word

echo "==> PASS: zisk_stateless_verdict_v2 debug probe emits, links, and formats through final word"
