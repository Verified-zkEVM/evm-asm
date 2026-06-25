#!/usr/bin/env bash
# Build the zisk_accel SPIKE extension (.so loaded via spike --extlib).
# Requires riscv-isa-sim checked out + built at $SPIKE_SRC.
set -euo pipefail
cd "$(dirname "$0")"
SPIKE_SRC="${SPIKE_SRC:-/Users/dhsorens/devel/riscv-isa-sim}"
BOOST_INC="${BOOST_INC:-/opt/homebrew/include}"
OUT="${OUT:-libziskaccel.so}"

[[ -d "$SPIKE_SRC/riscv" ]] || { echo "SPIKE_SRC=$SPIKE_SRC has no riscv/ — set SPIKE_SRC" >&2; exit 1; }

g++ -std=c++2a -O2 -fPIC -shared -Wall -Wno-unused-parameter \
  -undefined dynamic_lookup \
  -I"$SPIKE_SRC" \
  -I"$SPIKE_SRC/riscv" \
  -I"$SPIKE_SRC/fesvr" \
  -I"$SPIKE_SRC/softfloat" \
  -I"$SPIKE_SRC/build" \
  -I"$BOOST_INC" \
  zisk_accel.cc -o "$OUT"
echo "built $(pwd)/$OUT"
