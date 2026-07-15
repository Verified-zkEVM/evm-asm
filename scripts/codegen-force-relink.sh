#!/usr/bin/env bash
# Rebuild the native code generator from a fresh link before executing a KAT.
# A plain `lake build codegen` has previously replayed stale linked guest
# content, while each probe ELF is emitted anew by `lake exe codegen`.
set -euo pipefail
cd "$(dirname "$0")/.."
rm -f .lake/build/bin/codegen .lake/build/bin/codegen.hash .lake/build/bin/codegen.trace
lake build codegen
