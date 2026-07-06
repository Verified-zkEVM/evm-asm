#!/usr/bin/env bash
# Build the SPIKE backend for the stateless guest:
#   libziskaccel.so  — accelerator-CSR extension (for stock `spike --extlib`)
#   spike_run        — custom driver (ELF + input file -> 256-byte output file),
#                      a drop-in for `ziskemu -e <elf> -i <in> -o <out>`.
# Requires riscv-isa-sim checked out + built at $SPIKE_SRC, and a riscv64 as/ld.
set -euo pipefail
cd "$(dirname "$0")"
# Default to a riscv-isa-sim checkout sibling to this repo; override with SPIKE_SRC.
SPIKE_SRC="${SPIKE_SRC:-$(cd ../../.. && pwd)/riscv-isa-sim}"
SPIKE_BUILD="${SPIKE_BUILD:-$SPIKE_SRC/build}"
OS_NAME="$(uname -s)"

find_tool() {
  local env_name="$1"; shift
  local configured="${!env_name:-}"
  local candidate
  if [[ -n "$configured" ]]; then
    echo "$configured"
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

if [[ "$OS_NAME" == "Darwin" ]]; then
  BOOST_INC="${BOOST_INC:-/opt/homebrew/include}"
  AS="${RISCV_AS:-riscv64-elf-as}"
  LD="${RISCV_LD:-riscv64-elf-ld}"
  OBJCOPY="${RISCV_OBJCOPY:-riscv64-elf-objcopy}"
else
  AS="$(find_tool RISCV_AS riscv64-unknown-elf-as riscv64-elf-as)"
  LD="$(find_tool RISCV_LD riscv64-unknown-elf-ld riscv64-elf-ld)"
  OBJCOPY="$(find_tool RISCV_OBJCOPY riscv64-unknown-elf-objcopy riscv64-elf-objcopy)"
fi

[[ -d "$SPIKE_SRC/riscv" ]] || { echo "set SPIKE_SRC (no $SPIKE_SRC/riscv)" >&2; exit 1; }
[[ -f "$SPIKE_BUILD/libriscv.a" ]] || { echo "build spike first (no $SPIKE_BUILD/libriscv.a)" >&2; exit 1; }

if [[ "$OS_NAME" == "Darwin" ]]; then
  INCS=(-I"$SPIKE_SRC" -I"$SPIKE_SRC/riscv" -I"$SPIKE_SRC/fesvr" -I"$SPIKE_SRC/softfloat"
        -I"$SPIKE_BUILD" -I"$BOOST_INC" -I.)
else
  INCS=(-I"$SPIKE_SRC" -I"$SPIKE_SRC/riscv" -I"$SPIKE_SRC/fesvr" -I"$SPIKE_SRC/softfloat"
        -I"$SPIKE_BUILD" -I.)
fi
CXX_STD="-std=c++2a -O2 -Wall -Wno-unused-parameter"

if [[ "$OS_NAME" == "Darwin" ]]; then
  # Preserve the original macOS build commands.
  g++ $CXX_STD -fPIC -shared -undefined dynamic_lookup "${INCS[@]}" \
    zisk_accel.cc -o libziskaccel.so
  echo "built $(pwd)/libziskaccel.so"

  "$AS" -march=rv64imac_zicsr -o handler.o handler.s
  "$LD" -Ttext=0x60000000 -nostdlib -o handler.elf handler.o
  "${RISCV_OBJCOPY:-riscv64-elf-objcopy}" -O binary handler.elf handler.bin
  xxd -i handler.bin > handler_bin.h
  echo "generated handler_bin.h ($(wc -c < handler.bin | tr -d ' ') bytes)"

  g++ $CXX_STD "${INCS[@]}" \
    spike_run.cc zisk_accel.cc \
    "$SPIKE_BUILD"/libriscv.a "$SPIKE_BUILD"/libdisasm.a \
    "$SPIKE_BUILD"/libsoftfloat.a "$SPIKE_BUILD"/libfesvr.a "$SPIKE_BUILD"/libfdt.a \
    -L/opt/homebrew/lib -lpthread -lboost_regex \
    -o spike_run
  echo "built $(pwd)/spike_run"
else
  # 1) accelerator extension as a loadable .so (for stock spike)
  g++ $CXX_STD -fPIC -shared "${INCS[@]}" \
    zisk_accel.cc -lcrypto -o libziskaccel.so
  echo "built $(pwd)/libziskaccel.so"

  # 2) trap handler -> raw binary -> C header
  "$AS" -march=rv64imac_zicsr -o handler.o handler.s
  "$LD" -Ttext=0x60000000 -e _handler -nostdlib -o handler.elf handler.o
  "$OBJCOPY" -O binary handler.elf handler.bin
  xxd -i handler.bin > handler_bin.h
  echo "generated handler_bin.h ($(wc -c < handler.bin | tr -d ' ') bytes)"

  # 3) custom driver executable (links spike static libs)
  g++ $CXX_STD "${INCS[@]}" \
    spike_run.cc zisk_accel.cc \
    "$SPIKE_BUILD"/libriscv.a "$SPIKE_BUILD"/libdisasm.a \
    "$SPIKE_BUILD"/libsoftfloat.a "$SPIKE_BUILD"/libfesvr.a "$SPIKE_BUILD"/libfdt.a \
    -lpthread -lcrypto \
    -o spike_run
  echo "built $(pwd)/spike_run"
fi
