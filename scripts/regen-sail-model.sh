#!/usr/bin/env bash
# regen-sail-model.sh — reproducibly regenerate the scoped zkVM RISC-V Lean model.
#
# STATUS: SKELETON (staged 2026-06-24, pre-P1). Encodes the known pipeline recipe
# from docs/sail-zkvm-model-review.md §6. It does NOT yet run end-to-end — P1 (the
# regeneration spike) fills in the pinned commits/config and validates it; P2
# wires it into the vendored package + check-sail-pin.sh.
#
# Prerequisites (NOT assumed present; this is why P1 is its own session):
#   - OCaml + opam, building rems-project/sail FROM SOURCE (released Sail has no
#     Lean backend). See Lean_RV64D/README.md.
#   - z3, gmp, pkg-config, cmake.
#   - A clone of github.com/riscv/sail-riscv at the pinned commit.
#
# Usage:
#   scripts/regen-sail-model.sh --plan            # print the recipe, make no changes (default)
#   scripts/regen-sail-model.sh --run <build-dir> # P2+: actually generate (requires toolchain)
set -euo pipefail

MODE="${1:---plan}"

# --- Pins (filled in by P1; mirror sail-import/PROVENANCE.toml [target]) -------
SAIL_RISCV_COMMIT="TODO_P1"
SAIL_COMPILER_COMMIT="TODO_P1"
LEAN_SAIL_REV="TODO_P1"   # backend default v4; project on v3 — reconcile (review §1.1)

# --- The scoped RV64IM module closure (review §3) ------------------------------
# ~14 modules; core's type deps (A_types, Zicbop_types, Zicbom_types, PM_types)
# come in transitively.
SAIL_MODULES=(
  --module prelude --module core --module exceptions --module pmp --module sys
  --module I_types --module I_insts --module M_types --module M_insts
  --module postlude
)

CONFIG_FILE="sail-import/riscv64im_zicclsm.json"   # §4 keys; produced in P1

print_plan() {
  cat <<EOF
=== regen-sail-model.sh — PLAN (no changes made) ===

1. Build Sail from source (rems-project/sail @ ${SAIL_COMPILER_COMMIT}) with the
   Lean backend (opam pin add sail; dune build --release; dune install).

2. Clone riscv/sail-riscv @ ${SAIL_RISCV_COMMIT}.

3. Configure cmake with the scoped module list and the zkVM config, then build
   the Lean target (per sail-riscv/model/CMakeLists.txt:406-475):

     cmake -S sail-riscv -B <build> -DCMAKE_BUILD_TYPE=Release \\
       -DSAIL_MODULES="${SAIL_MODULES[*]}"
     cmake --build <build> --target generated_lean_rv64d
     # and, for differential testing (P3):
     cmake --build <build> --target generated_lean_executable_rv64d

   The scoped Lean lands under <build>/model/Lean_RV64D (+ _executable).
   Config consumed: ${CONFIG_FILE}.

4. P1 measures the generated 'Register' enum (sys vector/CSR residue, review §3)
   and confirms the decode is bv_decide-free (review §5.6).

5. P2 vendors the result under vendor/sail-riscv-zkvm-lean/, records the resolved
   commits/config hash in sail-import/PROVENANCE.toml [target], and points
   lakefile.toml at it.

Reconciliation note: backend targets lean4 v4.29.0 / lean-sail v4; project is on
v4.30.0-rc1 / v3. Resolve the compatible triple in P1 before vendoring.
EOF
}

case "$MODE" in
  --plan) print_plan ;;
  --run)
    echo "ERROR: --run is not implemented yet (skeleton). Complete P1, fill the" >&2
    echo "       pins above, then implement the steps printed by --plan." >&2
    exit 2 ;;
  *) echo "usage: $0 [--plan|--run <build-dir>]" >&2; exit 1 ;;
esac
