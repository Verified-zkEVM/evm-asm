#!/usr/bin/env bash
# regen-sail-model.sh — reproducibly regenerate the scoped zkVM RISC-V Lean model.
#
# STATUS: VALIDATED by the P1 regen spike (2026-06-24). The pins, the module
# selection mechanism, and the sail invocation below were exercised end-to-end in
# this environment. See docs/agents/sail-regen-spike.md for the go/no-go report
# and the measurements. P2 vendors the output under vendor/sail-riscv-zkvm-lean/
# and wires this into check-sail-pin.sh.
#
# KEY CORRECTIONS over the pre-P1 skeleton:
#   * Sail with the Lean backend is ALREADY installed (opam switch "sail",
#     sail 0.19.1, sail_lean_backend 0.19.1) — no build-from-source.
#   * Module scoping in Sail 0.19.1 is POSITIONAL (`sail … project main I_insts
#     M_insts`), NOT `--module X` and NOT cmake `-DSAIL_MODULES`. The cmake Lean
#     target hardcodes `--all-modules`, so we invoke `sail` directly.
#   * VERSION RECONCILIATION IS UNRESOLVED (P2 crux): the 0.19.1-emitted model
#     assumes lean-sail v4 (lean4 v4.29.0) and does NOT build drop-in against the
#     project's pinned lean-sail v3 on v4.30.0-rc1. See docs/agents/sail-regen-spike.md
#     "The version finding". This script only GENERATES the model; making it build
#     in-project is P2.
set -euo pipefail

MODE="${1:---plan}"

# --- Pins (resolved by P1; mirror sail-import/PROVENANCE.toml [target]) --------
SAIL_RISCV_COMMIT="1760ee2d14e123fc00e60a4f002a262fedcece14"  # last commit requiring Sail 0.19.1
SAIL_SWITCH="sail"            # opam switch holding sail 0.19.1 + sail_lean_backend
# lean-sail rev: UNRESOLVED. The 0.19.1 model needs ~v4 (79b4d08, lean4 v4.29.0),
# NOT the project's v3 (49ccc5a). P2 reconciles (see PROVENANCE.toml [target]).
LEAN_SAIL_REV="UNRESOLVED_P2"

# z3 (4.15.3) is required by Sail's typechecker and is NOT on PATH by default.
# Adjust if the nix store path changes.
Z3_BIN_DIR="/nix/store/x6z3sjmccszacl1xvdlpi7bd4ps7mhci-z3-4.15.3/bin"
SAIL_BIN_DIR="${SAIL_BIN_DIR:-$HOME/.opam/${SAIL_SWITCH}/bin}"

# --- The scoped RV64IM module selection (POSITIONAL; review §3 / spike §"how") -
# Sail pulls each module's `requires` closure in transitively. `main` reaches the
# fetch/decode/step loop via postlude; I_insts / M_insts add the integer + M
# instruction (scattered) clauses. Note: `sys` unavoidably drags in the V/FD
# register *state* (spike §2) — the state vector is ~163 ctors, not minimal.
SAIL_MODULES=(main I_insts M_insts)

CONFIG_FILE="sail-import/riscv64im_zicclsm.json"   # validated in P1 (passes validate_config.sail)

# Lean backend flags, mirroring sail-riscv model/CMakeLists.txt's lean target.
lean_flags() {
  local outdir="$1"
  printf '%s\n' \
    --lean --lean-output-dir "$outdir" --lean-force-output \
    --lean-non-beq-type instruction --lean-noncomputable \
    --lean-noncomputable-function encdec_forwards \
    --lean-noncomputable-function encdec_backwards \
    --lean-noncomputable-function encdec_forwards_matches \
    --lean-noncomputable-function encdec_backwards_matches \
    --lean-noncomputable-function encdec_compressed_forwards \
    --lean-noncomputable-function encdec_compressed_backwards \
    --lean-noncomputable-function encdec_compressed_forwards_matches \
    --lean-noncomputable-function encdec_compressed_backwards_matches \
    --lean-import-file ../handwritten_support/RiscvExtras.lean
}

print_plan() {
  cat <<EOF
=== regen-sail-model.sh — PLAN (no changes made) ===

Prereqs (validated present in the P1 environment):
  * opam switch "${SAIL_SWITCH}" with sail 0.19.1 (sail_lean_backend) at
    ${SAIL_BIN_DIR}
  * z3 4.15.3 at ${Z3_BIN_DIR}
  * a clone of github.com/riscv/sail-riscv @ ${SAIL_RISCV_COMMIT}

1. Clone + checkout sail-riscv:
     git clone https://github.com/riscv/sail-riscv.git
     git -C sail-riscv checkout ${SAIL_RISCV_COMMIT}

2. cmake CONFIGURE ONLY (emits config schema + finds toolchain; no build):
     cmake -S sail-riscv -B sail-riscv/build -DCMAKE_BUILD_TYPE=Release

3. Generate the scoped Lean model by invoking sail DIRECTLY (the cmake lean
   target hardcodes --all-modules; we override via positional modules):
     cd sail-riscv/model
     sail --strict-var --strict-bitvector --strict-exponentials \\
          --require-version 0.19.1 <lean-flags> \\
          --variable "TERMINATION_FILE = true" \\
          --config <repo>/${CONFIG_FILE} \\
          riscv.sail_project ${SAIL_MODULES[*]}

   Output: ~84 .lean files. Register enum ~163 ctors (incl. V/FD reg state).
   Decode is bv_decide-free (no --lean-matchbv).

4. P2 vendors the output under vendor/sail-riscv-zkvm-lean/, then RECONCILES the
   runtime: the 0.19.1 model needs lean-sail ~v4 (lean4 v4.29.0), NOT the project's
   v3, and v4 itself needs v4.30 fixes backported (getMsb, String.Slice, IntRange
   omega). See spike report "What P2 must decide". Then re-point the 51 *_sail_equiv
   lemmas (mind bool_to_bit -> bool_to_bits; diff vs the vendored model first).

Run with:  scripts/regen-sail-model.sh --run <out-dir>
EOF
}

do_run() {
  local outdir="${1:?usage: $0 --run <out-dir>}"
  local repo_root; repo_root="$(cd "$(dirname "$0")/.." && pwd)"
  local cfg="${repo_root}/${CONFIG_FILE}"
  [[ -f "$cfg" ]] || { echo "ERROR: config not found: $cfg" >&2; exit 2; }

  export PATH="${Z3_BIN_DIR}:${SAIL_BIN_DIR}:${PATH}"
  command -v sail >/dev/null || { echo "ERROR: sail not on PATH (expected in ${SAIL_BIN_DIR})" >&2; exit 2; }
  command -v z3   >/dev/null || { echo "ERROR: z3 not on PATH (expected in ${Z3_BIN_DIR})" >&2; exit 2; }

  local work; work="$(mktemp -d)"
  echo ">> cloning sail-riscv @ ${SAIL_RISCV_COMMIT} into ${work}" >&2
  git clone --quiet https://github.com/riscv/sail-riscv.git "${work}/sail-riscv"
  git -C "${work}/sail-riscv" checkout --quiet "${SAIL_RISCV_COMMIT}"

  echo ">> cmake configure (no build)" >&2
  cmake -S "${work}/sail-riscv" -B "${work}/sail-riscv/build" -DCMAKE_BUILD_TYPE=Release >/dev/null

  mkdir -p "$outdir"
  echo ">> generating scoped Lean model: ${SAIL_MODULES[*]}" >&2
  ( cd "${work}/sail-riscv/model"
    mapfile -t LF < <(lean_flags "$outdir")
    sail --strict-var --strict-bitvector --strict-exponentials --require-version 0.19.1 \
      "${LF[@]}" \
      --variable "TERMINATION_FILE = true" \
      --config "$cfg" \
      riscv.sail_project "${SAIL_MODULES[@]}" )

  echo ">> done. .lean files: $(find "$outdir" -name '*.lean' | wc -l) in ${outdir}" >&2
}

case "$MODE" in
  --plan) print_plan ;;
  --run)  shift; do_run "${1:-}" ;;
  *) echo "usage: $0 [--plan|--run <out-dir>]" >&2; exit 1 ;;
esac
